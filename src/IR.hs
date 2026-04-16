{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module IR (
  System (..),
  Process (..),
  Vertex (..),
  Edge (..),
  Port (..),
  Id (..),
  translate,
  filterUnused,
  makePort,
  isDelayVar,
  typeOrConstraint,
  delayVertex,
  delayProc,
)
where

import Control.Monad
import Data.List (sort)
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import GHC.Core
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.DataCon
import GHC.Core.Type
import GHC.Types.Name (Name, nameModule, getName, getOccString)
import GHC.Types.Unique (getUnique)
import GHC.Types.Var (isTyCoVar)
import GHC.Utils.Outputable (showPprUnsafe)
import GHC.Unit.Module (moduleName, moduleNameString)

import qualified Data.Graph as G
import Prettyprinter

data Id
  = Empty
  | Direct CoreBndr
  | Nested Id CoreBndr
  | Inline Id Int
  deriving (Ord)
instance Eq Id where
  (==) Empty Empty = False
  (==) (Direct i1) (Direct i2) = i1 == i2
  (==) (Nested i1 b1) (Nested i2 b2) = b1 == b2 && i1 == i2
  (==) (Inline i1 ix1) (Inline i2 ix2) = ix1 == ix2 && i1 == i2
  (==) _ _ = False
instance Show Id where
  show = \case
    Empty -> ""
    Direct binder -> getString binder
    Nested parent binder -> show parent <> "_" <> getString binder
    Inline parent ix -> show parent <> "_" <> show ix
    where
      getString binder = getOccString binder <> "_" <> (show . getUnique) binder
instance Pretty Id where
  pretty = unsafeViaShow

instance Semigroup Id where
  (<>) Empty i = i
  (<>) i Empty = i
  (<>) i (Direct b) = Nested i b
  (<>) i1 (Inline i2 ix) = Inline (i1 <> i2) ix
  (<>) i1 (Nested i2 b) = Nested (i1 <> i2) b

instance Monoid Id where
  mempty = Empty

showSloppy :: Id -> String
showSloppy = \case
  Empty -> ""
  Direct binder -> getOccString binder
  other -> show other

data System = System
  { inputs :: [Var]
  , outputs :: [Var]
  , processes :: [Process]
  , vertices :: [Vertex]
  , edges :: [Edge]
  , graph :: Maybe G.Graph
  , schedule :: Maybe [Int]
  }
instance Show System where
  show = show . pretty
instance Pretty System where
  pretty System{..} =
    nest 4 $
      pretty "System"
        <> tupled
          [ pretty "inputs =" <+> (pretty . showPprUnsafe) inputs
          , pretty "outputs =" <+> (pretty . showPprUnsafe) outputs
          , pretty processes
          , pretty vertices
          , pretty edges
          , pretty "dependencies =" <+> pretty (G.edges <$> graph)
          , case schedule of
              Just sched ->
                pretty "schedule ="
                  <+> pretty sched
              _ -> pretty "unschedulable"
          ]

-- A process constructor applied to a function, but not connected in a network.
data Process = Process
  { binder :: Id
  , inports :: [Port]
  , outports :: [Port]
  , appliedInternal :: [Id]
  , subsystem :: Maybe System
  , body :: CoreExpr
  }
instance Eq Process where
  (==) Process { binder = b1 } Process { binder = b2} = b1 == b2
instance Ord Process where
  compare Process { binder = b1 } Process { binder = b2} = compare b1 b2
instance Show Process where
  show = show . pretty
instance Pretty Process where
  pretty Process{..} =
    nest 4 $
      pretty "Process"
        <> tupled
          [ pretty binder
          , pretty "inports =" <+> pretty inports
          , pretty "outports =" <+> pretty outports
          , pretty "appliedInternal =" <+> pretty appliedInternal
          , maybe (braces . pretty . showPprUnsafe $ body) pretty subsystem
          ]

-- A process connected in a network.
-- It must therefore have at least an input and an output.
-- A vertex can only be referred to inside the same system, since it represents
-- an application of a process inside the system. This means the id only needs
-- to be unique inside the system.
data Vertex = Vertex
  { id :: Int
  , process :: Either Id Process
  , inputs :: [Var]
  , outputs :: [Var]
  }
instance Show Vertex where
  show = show . pretty
instance Pretty Vertex where
  pretty Vertex{id = i, ..} =
    nest 2 $
      pretty "Vertex"
        <> tupled
          [ pretty i
          , pretty "inputs =" <+> (pretty . showPprUnsafe) inputs
          , pretty "outputs =" <+> (pretty . showPprUnsafe) outputs
          , either (pretty . show) pretty process
          ]
instance Eq Vertex where
  (==) Vertex {id = id1} Vertex {id = id2} = id1 == id2
instance Ord Vertex where
  compare Vertex {id = id1} Vertex {id = id2} = compare id1 id2

-- An edge (signal) inside a system.
-- Can only refer to local vertices.
data Edge = Edge
  { binder :: !Var
  , source :: !Int
  , target :: !Int
  }
instance Show Edge where
  show = show . pretty
instance Pretty Edge where
  pretty Edge{..} =
    nest 2 $
      pretty "Edge"
        <> tupled
          [ (pretty . showPprUnsafe) binder
          , pretty source
          , pretty target
          ]

data Port
  = Opaque Type
  | Signal Port Type String
  | Vector Port Type

instance Show Port where
  show = show . pretty
instance Pretty Port where
  pretty = \case
    Opaque ty ->
      pretty "OpaquePort"
        <> (parens . pretty . showPprUnsafe) ty
    Signal inner _ _ ->
      pretty "SignalPort"
        <> (parens . pretty) inner
    Vector inner _ ->
      pretty "VectorPort"
        <> (parens . pretty) inner

translate :: CoreProgram -> System
translate f =
  System
    { inputs = []
    , outputs = []
    , processes
    , vertices = []
    , edges = []
    , graph = Nothing
    , schedule = Nothing
    }
 where
  processes = reverse . foldl' (makeProcesses Empty) [] . map Right $ f
  makeProcesses parent acc bind =
    case makeProcess parent acc bind of
      Nothing -> acc
      Just p -> p : acc

makePorts :: ([Type], [Type]) -> ([Port], [Port])
makePorts (inty, outty) =
  (inports, outports)
 where
  inports = map makePort inty
  outports = map makePort outty

makePort :: Type -> Port
makePort = \case
  t@(FunTy _ _ (TyVarTy v) ft_res) ->
    case getOccString v of
      "Signal" -> Signal (makePort ft_res) t (moduleString . getName $ v)
      "Vector" -> Vector (makePort ft_res) t
      "Matrix" -> Vector (Vector (makePort ft_res) t) t
      _ -> Opaque t
  t@(TyConApp con app) ->
    case (getOccString con, app) of
      ("Signal", t':_) -> Signal (makePort t') t (moduleString . tyConName $ con)
      ("Vector", t':_) -> Vector (makePort t') t
      ("Matrix", t':_) -> Vector (Vector (makePort t') t) t
      _ -> Opaque t
  t -> Opaque t

{- | Extract all arguments and returns
If the last return is a tuple type application, return the application list
-}
extractTypes :: [Type] -> Type -> ([Type], [Type])
extractTypes acc = \case
  ForAllTy _ ty -> extractTypes acc ty
  -- Discard constraints for now
  FunTy{ft_af = FTF_C_T, ft_res = res} ->
    extractTypes acc res
  FunTy{ft_af = FTF_C_C, ft_res = res} ->
    extractTypes acc res
  -- Add a non-constraint type
  FunTy{ft_arg = arg, ft_res = res} ->
    extractTypes (arg : acc) res
  t -> (reverse acc, extractConstructor [] t)
 where
  extractConstructor resacc = \case
    TyConApp v types | isTupleTyCon v -> reverse resacc <> types
    t -> reverse (t : resacc)

-- Strip all Lams so we don't need to bother with non-eta-reduced processes.
-- We con't count the type variables as those won't produce an App in the top
-- level definition.
stripLamApps :: CoreExpr -> CoreExpr
stripLamApps expr = case expr of
  -- Explicitly strips lambdas refering to type-level binders
  Lam b e | typeOrConstraint (Var b) -> stripLamApps e
  -- Also strip matching Lam App pairs
  Lam (arg) (App e (Var v)) | v == arg -> stripLamApps e
  _ -> expr

{- | Make a process from a binding.
A process should be self-contained, i.e. not have any communication outside
of its arguments and return.
-}
makeProcess :: Id -> [Process] -> Either (Int, CoreExpr, [Var], [Var]) CoreBind -> Maybe Process
makeProcess parent procs = \case
  Right (Rec _) -> Nothing
  Right (NonRec bind expr') ->
  -- A process needs at least an output. The case with no inputs is technically
  -- a signal, but this can be useful for e.g. generators.
    if length outports /= 0
      then
        Just
          Process
            { binder = Direct bind
            , inports
            , outports
            , subsystem
            , body
            , appliedInternal = case subsystem of
              Just _ -> []
              Nothing -> map Direct . getInternal procs [] $ body
            }
      else Nothing
    where
      body = stripLamApps expr'
      subsystem = translateExpr (Direct bind) procs body
      (inports, outports) = makePorts . extractTypes [] $ varType bind
  Left (ix, body, inputs, outputs) ->
        Just
          Process
            { binder = Inline parent ix
            , inports
            , outports
            , subsystem
            , body
            , appliedInternal = case subsystem of
              Just _ -> []
              Nothing -> map Direct . getInternal procs [] $ body
            }
    where
      (inports, outports) = makePorts (varType <$> inputs, varType <$> outputs)
      subsystem = translateExpr parent procs body

-- | Get all internal function applications of an expression
-- This is used to not filter out internal process applications
getInternal :: [Process] -> [CoreBndr] -> CoreExpr -> [CoreBndr]
getInternal procs acc = \case
  Let (NonRec _ e1) e2 ->
    let acc' = getInternal procs acc e1
     in getInternal procs acc' e2
  Let (Rec b) e2 ->
    let acc' = foldr (\(_, e1) a -> getInternal procs a e1) acc b
     in getInternal procs acc' e2
  Case _ _ _ alts ->
    foldr (\(Alt _ _ e1) a -> getInternal procs a e1) acc alts
  Lam _ e -> getInternal procs acc e
  Var v | not $ typeOrConstraint (Var v) -> v : acc
  App e1 e2 ->
    let acc' = getInternal procs acc e2
     in getInternal procs acc' e1
  _ -> acc

typeOrConstraint :: CoreExpr -> Bool
typeOrConstraint = \case
  Var v -> isTyCoVar v || (isPredTy . varType) v
  Type _ -> True
  _ -> False

moduleString :: Name -> String
moduleString = moduleNameString . moduleName . nameModule

translateExpr :: Id -> [Process] -> CoreExpr -> Maybe System
translateExpr parent procs expr' = out
 where
  (_, inputs', expr) = collectTyAndValBinders expr'
  inputs = filter (not . typeOrConstraint . Var) inputs'
  (binds, inputMap, sigs, outputs) = getSignals inputs [] [] expr
  apps' = map (getApplication binds) sigs
  apps = mapMaybe (resolveTuples apps') apps'
  processes =
    filter (\Process{binder} -> not $ elem binder (Direct <$> binds)) $
      getProcesses parent [] expr
  vertices =
    mapMaybe id . zipWith (makeVertex parent (procs <> processes)) [0 ..] $
      apps <> map (\(v, m) -> (Var v, [v], m)) inputMap
  edges = mconcat . map (makeEdge vertices) $ binds
  sEdges = mapMaybe (\Edge {source, target} ->
    if isDelayVertex (procs <> processes) vertices source
      then Nothing
      else Just $ (source, target)) edges
  graph = G.buildG (0, length vertices - 1) sEdges
  selfEdges = any (\Edge {source, target} -> source == target) edges
  schedulable = not selfEdges && (all (\(G.Node _ forest) -> forest == []) . G.scc $ graph)
  out =
    if length vertices /= 0
      then
        pure $
          System
            { inputs
            , outputs
            , processes
            , vertices
            , edges
            , graph = Just graph
            , schedule = if schedulable then pure $ G.topSort graph else Nothing
            }
      else Nothing

procsFromId :: Id -> [Process] -> [Process]
procsFromId var = filter (\Process { binder } -> binder == var)

isDelayVertex :: [Process] -> [Vertex] -> Int -> Bool
isDelayVertex processes vertices vid =
  case mapMaybe (delayVertex processes) . filter (\Vertex {id = i} -> i == vid) $ vertices of
    _ : [] -> True
    _ -> False

delayVertex :: [Process] -> Vertex -> Maybe Vertex
delayVertex processes v = case delayProc processes v of
  _ : _ -> Just v
  _ -> Nothing

delayProc :: [Process] -> Vertex -> [Process]
delayProc processes = \case
  Vertex { process = Right proc } ->
    if isDelayProcess proc then [proc] else []
  Vertex { process = Left var } ->
    filter isDelayProcess . procsFromId var $ processes

isDelayVar :: Var -> Bool
isDelayVar v =
  getOccString v == "delay"
    && ((moduleString . getName) v == "ForSyDe.Atom.MoC.SY.Lib")

isDelayProcess :: Process -> Bool
isDelayProcess Process { body } =
  case collectArgs body of
    (Var func, _args) -> isDelayVar func
    _ -> False

getProcesses :: Id -> [Process] -> CoreExpr -> [Process]
getProcesses parent acc = \case
  Lam _ e -> getProcesses parent acc e
  Let bind expr -> case makeProcess parent acc (Right bind) of
    Nothing -> getProcesses parent acc expr
    Just proc -> getProcesses parent (proc : acc) expr
  Case (Var _) _ _ (Alt (DataAlt dc) _ e : _) | isTupleDataCon dc ->
    getProcesses parent acc e
  -- Function composition
  App (App (App (App (App (Var v) _) _) _) e1) e2 | "." == (getOccString . getName) v ->
    let procs = getProcesses parent acc e1
     in getProcesses parent procs e2
  _ -> acc

{- | Get the applied signals of a subsystem
These will later be used to derive vertices and edges
-}
getSignals ::
  [CoreBndr] ->
  [(CoreBndr, [CoreBndr])] ->
  [(CoreBndr, CoreExpr)] ->
  CoreExpr ->
  ([CoreBndr], [(CoreBndr, [CoreBndr])], [(CoreBndr, CoreExpr)], [CoreBndr])
getSignals bindacc inputAcc acc = \case
  -- A signal should be fully applied, i.e. it should not have any input argument
  Let (NonRec b e) inExpr
    | isSignal (b, e) ->
        getSignals (b : bindacc) inputAcc ((b, e) : acc) inExpr
  -- Likely a process, handled separately
  Let (NonRec _ _) inExpr
    | otherwise ->
        getSignals bindacc inputAcc acc inExpr
  -- A Rec binding should not contain any process since they are supposed to be
  -- self-contained. Therefore filter binds with inputs.
  Let (Rec sigs) inExpr ->
    let sigs' = filter isSignal sigs
        b = map fst sigs'
     in getSignals (b <> bindacc) inputAcc (sigs' <> acc) inExpr
  Lam a e ->
    if typeOrConstraint (Var a)
      then getSignals bindacc inputAcc acc e
      else getSignals (a : bindacc) inputAcc acc e
  -- Add any top-level deconstructed input tuple mapping
  Case (Var v) _ _ (Alt (DataAlt dc) b e : _) | elem v bindacc && isTupleDataCon dc ->
    getSignals (b <> bindacc) ((v, b) : inputAcc) acc e
  Var v -> (bindacc, inputAcc, acc, [v])
  -- May be a tuple construction
  e ->
    let (e', args) = collectArgs e
        argvars =
          mapMaybe
            ( \case
                Var v | not $ typeOrConstraint (Var v) -> Just v
                _ -> Nothing
            )
            args
     in case e' of
      -- Is this actually a tuple constructor?
      Var i | (>1) . length . snd . extractTypes [] $ varType i ->
        (bindacc, inputAcc, acc, argvars)
      _ -> (bindacc, inputAcc, acc, [])
  where
    isSignal = (0 ==) . length . fst . extractTypes [] . varType . fst

-- | Resolve an application to a process, inputs and (potentially tupled) output
getApplication ::
  [CoreBndr] ->
  (CoreBndr, CoreExpr) ->
  (CoreExpr, [Var], Var, Maybe Var)
getApplication binds (output, expr) = (proc, input, output, splitTuples)
 where
  (input, splitTuples, proc) = stripSigApps ([], Nothing) expr
  stripSigApps (inputs, split) = \case
    App e (Var arg)
      | elem arg binds ->
          stripSigApps (arg : inputs, split) e
    e@(Case (Var arg) _b _t ((Alt _ _ _e) : _))
      | elem arg binds ->
          (inputs, Just arg, e)
    e -> (inputs, split, e)

-- | Resolve tupled outputs to their actual output signals
resolveTuples ::
  [(CoreExpr, [Var], Var, Maybe Var)] ->
  (CoreExpr, [Var], Var, Maybe Var) ->
  Maybe (CoreExpr, [Var], [Var])
resolveTuples _ (_, _, _, Just _) = Nothing
resolveTuples apps (proc, inputs, output, _) = Just (proc, inputs, outputs)
 where
  splits =
    mapMaybe
      ( \(p, _, out, tup) ->
          case tup of
            Just tuple | output == tuple -> Just (p, out)
            _ -> Nothing
      )
      apps
  outputs' = map snd . sort . mapMaybe getPos $ splits
  outputs = if length outputs' /= 0 then outputs' else [output]
  getPos :: (CoreExpr, Var) -> Maybe (Int, Var)
  getPos (expr, var) = case expr of
    (Case _ _ _ ((Alt _ args (Var out)) : _)) ->
      lookup out (zip args (zip [0 ..] $ repeat var))
    _ -> Nothing

makeVertex :: Id -> [Process] -> Int -> (CoreExpr, [Var], [Var]) -> Maybe Vertex
makeVertex parent procs ix = \case
  -- An application of a non-inline process
  (Var bind, inputs, outputs) ->
    Just $ Vertex
      { id = ix
      , process = Left (Direct bind)
      , inputs
      , outputs
      }
  -- An application of an inline process definition
  (expr, inputs, outputs) -> do
    process <- liftM Right $ makeProcess parent procs (Left (ix, expr, inputs, outputs))
    pure $ Vertex
      { id = ix
      , process
      , inputs
      , outputs
      }

makeEdge :: [Vertex] -> CoreBndr -> [Edge]
makeEdge vertices bind = [Edge bind] <*> source <*> targets
 where
  source = [i | Vertex{id = i, outputs} <- vertices, bind `elem` outputs]
  targets = [i | Vertex{id = i, inputs} <- vertices, bind `elem` inputs]

-- | Gather all processes referenced by the one corresponding to the string
filterUnused :: String -> System -> Maybe (Process, [Process])
filterUnused procname System { .. } =
  case filter (procNamed procname) processes of
    p@Process { .. } : _ ->
      let internal' = S.elems . findInternal (S.fromList processes) $ p
          internal = mconcat . map (getUsedAndLiftNested $ S.fromList processes) $ internal'
       in case subsystem of
        Just s ->
          let (subsys, used) = filterUnusedSystem (S.fromList processes, mempty) s
           in Just (p { subsystem = Just subsys }, S.elems (used <> internal))
        _ -> Just (p, S.elems internal)
    _ -> Nothing
  where
    procNamed name Process { binder } = showSloppy binder == name

filterUnusedSystem :: (S.Set Process, S.Set Process) -> System -> (System, S.Set Process)
filterUnusedSystem (reachable, used) s@System { .. } =
  (s { processes = [], vertices = vertices' }, subsysUsed)
  where
    processSet = S.fromList processes
    subsysUsed = (mconcat . S.elems . S.map (getUsedAndLiftNested reachable)) used'
    used' = usedByVertices used vertices
    usedByVertices acc = (acc <>) . mconcat . map vertexProcs
    vertices' = map removeInline vertices
    vertexProcs Vertex { process } = case process of
      Left p ->
        let procs = findProc p (reachable <> processSet)
            internalApps = (mconcat . S.elems . S.map (findInternal $ reachable <> processSet)) procs
         in procs <> internalApps
      Right p ->
        let internalApps = (findInternal $ reachable <> processSet) p
         in S.singleton p <> internalApps
    removeInline v@Vertex { process } = case process of
      Right Process { binder } -> v { process = Left binder }
      _ -> v

-- findProc :: (Foldable t, Monoid (f Process), Applicative f) => Id -> t Process -> f Process
-- findProc vid = foldMap (\p@Process { binder = i } -> if vid == i then pure p else mempty)

findProc :: Id -> S.Set Process -> S.Set Process
findProc var = S.filter (\Process { binder } -> binder == var)
findInternal :: S.Set Process -> Process -> S.Set Process
findInternal reachable Process {appliedInternal} =
  mconcat $ findProc <$> appliedInternal <*> [reachable]

getUsedAndLiftNested :: S.Set Process -> Process -> S.Set Process
getUsedAndLiftNested reachable p@Process { .. } = S.singleton p { subsystem = subsys } <> subsysUsed'
  where
    (subsys, subsysUsed') = case subsystem of
      Just s' -> (\(a, b) -> (Just a, b)) . filterUnusedSystem (reachable, mempty) $ s'
      Nothing -> (Nothing, mempty)
