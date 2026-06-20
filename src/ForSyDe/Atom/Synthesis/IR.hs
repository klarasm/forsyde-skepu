{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE DeriveDataTypeable #-}

module ForSyDe.Atom.Synthesis.IR (
  System (..),
  Process (..),
  Vertex (..),
  Edge (..),
  Port (..),
  Id (..),
  Synthesizable (..),
  translate,
  filterUnused,
  makePort,
  makePorts,
  isDelayVar,
  typeOrConstraint,
  procsFromId,
  vertexProcs,
  extractTypes,
)
where

import Data.Data (Data, Typeable)
import Data.List (sort)
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import GHC.Core
import GHC.Core.DataCon
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Types.Name (Name, getName, getOccString, nameModule)
import GHC.Types.Unique (getUnique)
import GHC.Types.Var (isTyCoVar)
import GHC.Unit.Module (moduleName, moduleNameString)
import GHC.Utils.Outputable (showPprUnsafe)

import qualified Data.Graph as G
import Prettyprinter

data Id a
  = Empty
  | Direct CoreBndr
  | Nested (Id a) (Id a)
  | Ix Int
  | ExId a
  deriving (Data, Typeable)
instance (Ord a) => Ord (Id a) where
  compare Empty Empty = LT
  compare Empty _ = LT
  compare (Ix ix1) (Ix ix2) = compare ix1 ix2
  compare (Ix _) _ = LT
  compare (Direct b1) (Direct b2) = compare b1 b2
  compare (Direct _) _ = LT
  compare (Nested na1 na2) (Nested nb1 nb2) = case compare na1 nb1 of
    EQ -> compare na2 nb2
    o -> o
  compare (Nested _ _) _ = LT
  compare (ExId e1) (ExId e2) = compare e1 e2
  compare _ Empty = GT
  compare _ (Ix _) = GT
  compare _ (Direct _) = GT
  compare _ (Nested _ _) = GT
instance (Eq a) => Eq (Id a) where
  (==) Empty _ = False
  (==) _ Empty = False
  (==) (Direct i1) (Direct i2) = i1 == i2
  (==) (Nested i1 b1) (Nested i2 b2) = b1 == b2 && i1 == i2
  (==) (Ix ix1) (Ix ix2) = ix1 == ix2
  (==) (ExId n1) (ExId n2) = n1 == n2
  (==) _ _ = False
instance (Pretty a) => Pretty (Id a) where
  pretty = \case
    Empty -> mempty
    Direct binder -> getString binder
    Nested (ExId e1) (ExId e2) -> pretty e1 <> pretty e2
    Nested e1@(Nested _ (ExId _)) (ExId e2) -> pretty e1 <> pretty e2
    Nested parent binder -> pretty parent <> pretty "_" <> pretty binder
    Ix ix -> pretty ix
    ExId n -> pretty n
   where
    getString binder =
      (pretty . getOccString) binder
        <> pretty "_"
        <> (pretty . show . getUnique) binder
instance (Pretty a) => Show (Id a) where
  show = show . pretty

instance Semigroup (Id a) where
  (<>) Empty i = i
  (<>) i Empty = i
  (<>) i1 (Nested i2 i3) = Nested (i1 <> i2) i3
  (<>) i1 i2 = Nested i1 i2

instance Monoid (Id a) where
  mempty = Empty

instance Functor Id where
  fmap f (Nested a b) = Nested (fmap f a) (fmap f b)
  fmap f (ExId a) = ExId (f a)
  fmap _ Empty = Empty
  fmap _ (Direct a) = Direct a
  fmap _ (Ix a) = Ix a

instance Applicative Id where
  pure a = ExId a
  (ExId f) <*> a = f <$> a
  (Nested f1 f2) <*> (Nested a1 a2) = Nested (f1 <*> a1) (f2 <*> a2)
  (Nested f1 f2) <*> a = Nested (f1 <*> a) (f2 <*> a)
  f <*> Nested a1 a2 = Nested (f <*> a1) (f <*> a2)
  Empty <*> _ = Empty
  Direct i <*> _ = Direct i
  Ix i <*> _ = Ix i

showSloppy :: (Pretty a) => (Id a) -> String
showSloppy = \case
  Empty -> ""
  Direct binder -> getOccString binder
  other -> show other

-- | A system containing mainly processes, vertices and edges.
data System = System
  { inputs :: [Var] -- ^ The system input binders
  , outputs :: [Var] -- ^ The system output binders
  , processes :: [Process] -- ^ Processes defined in the system
  , vertices :: [Vertex] -- ^ Vertices inside the system
  , edges :: [Edge] -- ^ Edges between vertices local to the system
  , graph :: Maybe G.Graph -- ^ Dependencies excluding delay edges
  , schedule :: Maybe [Int] -- ^ A schedule if one can be computed
  }
  deriving (Data, Typeable)
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

-- | A process constructor applied to a function, but not connected in a network.
data Process = Process
  { binder :: Id () -- ^ The constructed Id of the process, either from a
                    -- or constructed from parent system Ids Core binder
  , inports :: [Port] -- ^ The input types of the system
  , outports :: [Port] -- ^ The output types of the system
  , appliedInternal :: S.Set (Id ()) -- ^ Internal applications of binders
  , subsystem :: Maybe System -- ^ A subsystem if it exists
  , body :: CoreExpr -- ^ The body of the process
  }
  deriving (Data, Typeable)
instance Eq Process where
  (==) Process{binder = b1} Process{binder = b2} = b1 == b2
instance Ord Process where
  compare Process{binder = b1} Process{binder = b2} = compare b1 b2
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
          , pretty "appliedInternal =" <+> (pretty . S.elems) appliedInternal
          , maybe (braces . pretty . showPprUnsafe $ body) pretty subsystem
          ]

-- | A process connected in a network.
-- It must therefore have at least an output.
-- A vertex can only be referred to inside the same system, since it represents
-- an application of a process inside the system. This means the id only needs
-- to be unique inside the system.
data Vertex = Vertex
  { id :: Int -- ^ The Id of the vertex. It is only unique within its system
  , process :: Either (Id ()) Process -- ^ The Id of the applied process or its
                                      -- definition if inline
  , inputs :: [Var] -- ^ Input signals
  , outputs :: [Var] -- ^ Output signals
  , delay :: Bool -- ^ If the vertex delays its output
  }
  deriving (Data, Typeable)
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
  (==) Vertex{id = id1} Vertex{id = id2} = id1 == id2
instance Ord Vertex where
  compare Vertex{id = id1} Vertex{id = id2} = compare id1 id2

-- | An edge (signal) inside a system. Can only refer to local vertices.
data Edge = Edge
  { binder :: Var -- ^ The Core binder of the signal
  , source :: Int -- ^ The source vertex
  , target :: Int -- ^ The target vertex
  }
  deriving (Data, Typeable)
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

-- | A repackaging of the Core types for easier recognition
data Port
  = Opaque Type -- ^ A plain Core type
  | AbstExt Port Type -- ^ The representation of a presence or absence of an event
  | Signal Port Type String -- ^ A signal type with its module string
  | Vector Port Type -- ^ A vector type
  deriving (Data, Typeable)

instance Show Port where
  show = show . pretty
instance Pretty Port where
  pretty = \case
    Opaque ty ->
      pretty "OpaquePort"
        <> (parens . pretty . showPprUnsafe) ty
    AbstExt inner _ ->
      pretty "AbstExtPort"
        <> (parens . pretty) inner
    Signal inner _ _ ->
      pretty "SignalPort"
        <> (parens . pretty) inner
    Vector inner _ ->
      pretty "VectorPort"
        <> (parens . pretty) inner

-- | Translate a Core program into a top-level system. The top-level system
-- itself only contains a list of processes.
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

-- | Helper to process the output of extractTypes into Ports
makePorts :: ([Type], [Type]) -> ([Port], [Port])
makePorts (inty, outty) =
  (inports, outports)
 where
  inports = map makePort inty
  outports = map makePort outty

-- | Reconstruct a Core type into a Port
makePort :: Type -> Port
makePort = \case
  t@(FunTy _ _ (TyVarTy v) ft_res) ->
    case getOccString v of
      "Signal" -> Signal (makePort ft_res) t (moduleString . getName $ v)
      "AbstExt" -> AbstExt (makePort ft_res) t
      "Vector" -> Vector (makePort ft_res) t
      "Matrix" -> Vector (Vector (makePort ft_res) t) t
      _ -> Opaque t
  t@(TyConApp con app) ->
    case (getOccString con, app) of
      ("Signal", t' : _) -> Signal (makePort t') t (moduleString . tyConName $ con)
      ("AbstExt", t' : _) -> AbstExt (makePort t') t
      ("Vector", t' : _) -> Vector (makePort t') t
      ("Matrix", t' : _) -> Vector (Vector (makePort t') t) t
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

-- | Strip Apps matching with the binders from stripLams
stripApps :: ([CoreBndr], CoreExpr) -> Maybe CoreExpr
-- If we have an empty binder list the eta-reduce succeeded
stripApps ([], expr) = Just expr
stripApps ((x : xs), expr) = case expr of
  -- Matched argument in the correct order, eta-reduce is well-formed so far
  App e (Var a) | x == a -> stripApps (xs, e)
  -- We can't match the applied argument in the right order. Cannot eta-reduce
  -- while keeping semantics.
  _ -> Nothing

-- | Attempt to strip matching Lam App pairs (perform an eta-reduce)
stripLamApps :: CoreExpr -> CoreExpr
stripLamApps expr = case expr of
  Lam _ _ -> case stripApps . (\(b, e) -> (reverse b, e)) . collectBinders $ expr of
    Just e -> stripLamApps e
    Nothing -> expr
  _ -> expr

{- | Make a process from a binding.
A process should be self-contained, i.e. not have any communication outside
of its arguments and return.
-}
makeProcess :: Id a -> [Process] -> Either (Int, CoreExpr, [Var], [Var]) CoreBind -> Maybe Process
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
                Just _ -> mempty
                Nothing -> S.map Direct . getInternal procs mempty $ body
            }
      else Nothing
   where
    body = stripLamApps expr'
    subsystem = translateExpr (Direct bind) procs body
    (inports, outports) = makePorts . extractTypes [] $ varType bind
  Left (ix, body, inputs, outputs) ->
    Just
      Process
        { binder = const () <$> parent <> Ix ix
        , inports
        , outports
        , subsystem
        , body
        , appliedInternal = case subsystem of
            Just _ -> mempty
            Nothing -> S.map Direct . getInternal procs mempty $ body
        }
   where
    (inports, outports) = makePorts (varType <$> inputs, varType <$> outputs)
    subsystem = translateExpr (parent <> Ix ix) procs body

{- | Get all internal function applications of an expression
This is used to not filter out internal process applications
-}
getInternal :: [Process] -> S.Set CoreBndr -> CoreExpr -> S.Set CoreBndr
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
  Var v | not $ typeOrConstraint (Var v) -> S.singleton v <> acc
  App e1 e2 ->
    let acc' = getInternal procs acc e2
     in getInternal procs acc' e1
  _ -> acc

-- | Is this a type, type variable, or constraint/predicate (e.g. Num a)?
typeOrConstraint :: CoreExpr -> Bool
typeOrConstraint = \case
  Var v -> isTyCoVar v || (isPredTy . varType) v
  Type _ -> True
  _ -> False

-- | Helper to get the module of a Name
moduleString :: Name -> String
moduleString = moduleNameString . moduleName . nameModule

-- | Traverse an expression and try to make a system out of it with at least
-- one vertex.
translateExpr :: Id a -> [Process] -> CoreExpr -> Maybe System
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
  dependencies =
    mapMaybe
      ( \Edge{source, target} ->
          if isDelayVertex vertices source
            then Nothing
            else Just $ (source, target)
      )
      edges
  graph = G.buildG (0, length vertices - 1) dependencies
  -- If there are no self-edges and there are no strongly-connected componets
  -- the graph is a DAG, meaning topological sort can produce a valid schedule
  selfEdges = any (\Edge{source, target} -> source == target) edges
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

-- | Find processes matching the supplied Id
procsFromId :: Id a -> [Process] -> [Process]
procsFromId var = filter (\Process{binder} -> binder == (const () <$> var))

-- | True if the integer matches with a delay vertex in the provided list
isDelayVertex :: [Vertex] -> Int -> Bool
isDelayVertex vertices vid =
  case filter (\Vertex{id = i, delay} -> i == vid && delay) $ vertices of
    _ : [] -> True
    _ -> False

-- | True if the Core binder's string is delay and comes from ForSyDe-Atom
-- synchronous MoC
isDelayVar :: Var -> Bool
isDelayVar v =
  getOccString v == "delay"
    && ((moduleString . getName) v == "ForSyDe.Atom.MoC.SY.Lib")

-- | True if the process is applying a delay Var
isDelayProcess :: Process -> Bool
isDelayProcess Process{body} = isDelayExpr body
 where
  isDelayExpr = \case
    App (App (Var delay) _) _ -> isDelayVar delay
    App (App (App (App (App (Var composition) t1) t2) t3) e1) e2
      | typeOrConstraint t1 && typeOrConstraint t2 && typeOrConstraint t3
        && getOccString composition == "."
          -> isDelayExpr e1 || isDelayExpr e2
    _ -> False

-- | Traverse an expression and create processes. Note that this will create
-- processes for all non-recursive Let binds, meaning the output has to be
-- filtered for signals.
getProcesses :: Id a -> [Process] -> CoreExpr -> [Process]
getProcesses parent acc = \case
  Lam _ e -> getProcesses parent acc e
  Let bind expr -> case makeProcess parent acc (Right bind) of
    Nothing -> getProcesses parent acc expr
    Just proc -> getProcesses parent (proc : acc) expr
  Case (Var _) _ _ (Alt (DataAlt dc) _ e : _)
    | isTupleDataCon dc ->
        getProcesses parent acc e
  -- Function composition
  App (App (App (App (App (Var v) _) _) _) e1) e2
    | "." == (getOccString . getName) v ->
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
  -- Add any top-level deconstructed input tuple mapping
  Case (Var v) _ _ (Alt (DataAlt dc) b e : _)
    | elem v bindacc && isTupleDataCon dc ->
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
          Var i
            | (> 1) . length . snd . extractTypes [] $ varType i ->
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

-- | Make a process from an expression, input binds and output binds
makeVertex :: Id a -> [Process] -> Int -> (CoreExpr, [Var], [Var]) -> Maybe Vertex
makeVertex parent procs ix = \case
  -- An application of a non-inline process
  (Var bind, inputs, outputs) ->
    Just $
      Vertex
        { id = ix
        , process = Left (Direct bind)
        , inputs
        , outputs
        , delay = case filter isDelayProcess . procsFromId (Direct bind) $ procs of
          [] -> False
          _ -> True
        }
  -- An application of an inline process definition
  (expr, inputs, outputs) -> do
    proc <- makeProcess parent procs (Left (ix, expr, inputs, outputs))
    let process = Right proc
    pure $
      Vertex
        { id = ix
        , process
        , inputs
        , outputs
        , delay = isDelayProcess proc
        }

-- | Match binders with targets and source from vertices. Note that multiple
-- sources should never happen in practice. While GHC Uniques are not
-- guarranteed to actually be unique and can shadow, this should never happen
-- inside a system definition and should generate an error prior to Core
-- generation. Should this happen anyway, it will likely produce a self-edge
-- meaning the system won't be schedulable.
makeEdge :: [Vertex] -> CoreBndr -> [Edge]
makeEdge vertices bind = [Edge bind] <*> source <*> targets
 where
  source = [i | Vertex{id = i, outputs} <- vertices, bind `elem` outputs]
  targets = [i | Vertex{id = i, inputs} <- vertices, bind `elem` inputs]

-- | Gather all processes referenced by the one corresponding to the string
filterUnused :: String -> System -> Maybe (Process, [Process])
filterUnused procname System{..} =
  case filter (procNamed procname) processes of
    p@Process{..} : _ ->
      let internal' = S.elems . findInternal (S.fromList processes) $ p
          internal = mconcat . map (getUsedAndLiftNested $ S.fromList processes) $ internal'
       in case subsystem of
            Just s ->
              let (subsys, used) = filterUnusedSystem (S.fromList processes, mempty) s
               in Just (p{subsystem = Just subsys}, S.elems (used <> internal))
            _ -> Just (p, S.elems internal)
    _ -> Nothing
 where
  procNamed name Process{binder} = showSloppy binder == name

-- | Gather all processes referenced and lift them
filterUnusedSystem :: (S.Set Process, S.Set Process) -> System -> (System, S.Set Process)
filterUnusedSystem (reachable, used) s@System{..} =
  (s{processes = [], vertices = vertices'}, subsysUsed)
 where
  processSet = S.fromList processes
  subsysUsed = (mconcat . S.elems . S.map (getUsedAndLiftNested reachable)) used'
  used' = usedByVertices used vertices
  usedByVertices acc = (acc <>) . mconcat . map (vertexProcs $ reachable <> processSet)
  vertices' = map removeInline vertices
  removeInline v@Vertex{process} = case process of
    Right Process{binder} -> v{process = Left binder}
    _ -> v

-- | Helper to find processes matchin an Id in a Set, similar to procsFromId
findProc :: Id a -> S.Set Process -> S.Set Process
findProc var = S.filter (\Process{binder} -> binder == (const () <$> var))

-- | Helper to find processes from internal references
findInternal :: S.Set Process -> Process -> S.Set Process
findInternal reachable Process{appliedInternal} =
  mconcat $ findProc <$> S.elems appliedInternal <*> [reachable]

-- | Find processes referenced by a vertex or its inline process definition
vertexProcs :: S.Set Process -> Vertex -> S.Set Process
vertexProcs reachable Vertex{process} = case process of
  Left p ->
    let procs = findProc p reachable
        internalApps = (mconcat . S.elems . S.map (findInternal $ reachable)) procs
     in procs <> internalApps
  Right p ->
    let internalApps = (findInternal $ reachable) p
     in S.singleton p <> internalApps

-- | Lift all used processes while updating the subsystem to remove locals
getUsedAndLiftNested :: S.Set Process -> Process -> S.Set Process
getUsedAndLiftNested reachable p@Process{..} = S.singleton p{subsystem = subsys} <> subsysUsed'
 where
  (subsys, subsysUsed') = case subsystem of
    Just s' -> (\(a, b) -> (Just a, b)) . filterUnusedSystem (reachable, mempty) $ s'
    Nothing -> (Nothing, mempty)

class Synthesizable a where
  -- may need to resolve a previously unresolved process as dependency
  synthesize :: [Process] -> Process -> ([a], [a]) -> ([a], [a])
  compose :: ([a], [a]) -> a
