{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module IR (
  System (..),
  Process (..),
  Vertex (..),
  Edge (..),
  Port (..),
  translate,
)
where

import Control.Monad
import Data.List (sort)
import Data.Maybe (mapMaybe)
import GHC.Core
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.DataCon
import GHC.Core.Type
import GHC.Types.Var (isTyCoVar)
import GHC.Types.Name (getName, getOccString)
import GHC.Utils.Outputable (showPprUnsafe)

import qualified Data.Graph as G

data System = System
  { inputs :: [Var]
  , outputs :: [Var]
  , processes :: [Process]
  , vertices :: [Vertex]
  , edges :: [Edge]
  , graph :: Maybe G.Graph
  }
instance Show System where
  show System{..} =
    "System(inputs = "
      <> showPprUnsafe inputs
      <> ", outputs = "
      <> showPprUnsafe outputs
      <> ", "
      <> (unlines . map ("\t" <>) . lines . concat . map (("\n" <>) . show) $ processes)
      <> ", "
      <> (unlines . map ("\t" <>) . lines . concat . map (("\n" <>) . show) $ vertices)
      <> ", "
      <> (unlines . map ("\t" <>) . lines . concat . map (("\n" <>) . show) $ edges)
      <> ", "
      <> (show $ G.topSort <$> graph)
      <> ", "
      <> (show $ G.scc <$> graph)
      <> ")"

-- A process constructor applied to a function, but not connected in a network.
data Process = Process
  { binder :: Maybe CoreBndr
  , inports :: [Port]
  , outports :: [Port]
  , subsystem :: Maybe System
  , body :: CoreExpr
  }
instance Show Process where
  show Process{..} =
    "Process("
      <> showPprUnsafe binder
      <> ", inports = "
      <> show inports
      <> ", outports = "
      <> show outports
      <> ", "
      <> maybe ("{" <> showPprUnsafe body <> "}") show subsystem
      <> ")"

-- A process connected in a network.
-- It must therefore have at least an input and an output.
-- A vertex can only be referred to inside the same system, since it represents
-- an application of a process inside the system. This means the id only needs
-- to be unique inside the system.
data Vertex = Vertex
  { id :: Int
  , process :: Either Var Process
  , inputs :: [Var]
  , outputs :: [Var]
  }
instance Show Vertex where
  show Vertex{id = i, ..} =
    "Vertex("
      <> show i
      <> ", inputs = "
      <> showPprUnsafe inputs
      <> ", outputs = "
      <> showPprUnsafe outputs
      <> ", "
      <> either showPprUnsafe show process
      <> ")"
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
  show Edge{..} =
    "Edge("
      <> showPprUnsafe binder
      <> ", "
      <> show source
      <> ", "
      <> show target
      <> ")"

data Port = Port
  { ty :: Type
  }
instance Show Port where
  show Port{..} =
    "Port(" <> showPprUnsafe ty <> ")"

translate :: CoreProgram -> System
translate f =
  System
    { inputs = []
    , outputs = []
    , processes
    , vertices = []
    , edges = []
    , graph = Nothing
    }
 where
  processes = foldr makeProcesses [] . map Right $ f
  makeProcesses bind acc =
    case makeProcess acc bind of
      Nothing -> acc
      Just p -> p : acc

makePorts :: ([Type], [Type]) -> ([Port], [Port])
makePorts (inty, outty) =
  (inports, outports)
 where
  inports = map Port inty
  outports = map Port outty

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

{- | Make a process from a binding.
A process should be self-contained, i.e. not have any communication outside
of its arguments and return.
-}
makeProcess :: [Process] -> Either (CoreExpr, [Var], [Var]) CoreBind -> Maybe Process
makeProcess procs = \case
  Right (Rec _) -> Nothing
  Right (NonRec bind expr) ->
  -- A process needs both an input and an output. A function with just an
  -- output is a value
    if length inports /= 0 && length outports /= 0
      then
        Just
          Process
            { binder = Just bind
            , inports
            , outports
            , subsystem = translateExpr procs expr
            , body = expr
            }
      else Nothing
   where
    (inports, outports) = makePorts . extractTypes [] $ varType bind
  Left (expr, inputs, outputs) ->
        Just
          Process
            { binder = Nothing
            , inports = map (Port . varType) inputs
            , outports = map (Port . varType) outputs
            , subsystem = translateExpr procs expr
            , body = expr
            }

typeOrConstraint :: Var -> Bool
typeOrConstraint v = isTyCoVar v || (isPredTy . varType) v

translateExpr :: [Process] -> CoreExpr -> Maybe System
translateExpr procs expr' = out
 where
  (_, inputs', expr) = collectTyAndValBinders expr'
  inputs = filter (not . typeOrConstraint) inputs'
  (binds, inputMap, sigs, outputs) = getSignals inputs [] [] expr
  apps' = map (getApplication binds) sigs
  apps = mapMaybe (resolveTuples apps') apps'
  processes = getProcesses [] expr
  vertices =
    mapMaybe id $
      zipWith (makeVertex (procs <> processes)) [0 ..] $
        apps
          <> map (\v -> (Var v, [], [v])) inputs
          <> map (\(v, m) -> (Var v, [v], m)) inputMap
          <> map (\v -> (Var v, [v], [])) outputs
  edges = mconcat . map (makeEdge vertices) $ binds
  minVert = foldr1 min vertices
  maxVert = foldr1 max vertices
  sEdges = mapMaybe (\Edge {source, target} ->
    if isDelayVertex source then Nothing else Just $ (source, target)) edges
  graph = G.buildG (minVert.id, maxVert.id) sEdges
  isDelayVertex vid = case filter (\Vertex {id = pid} -> pid == vid) vertices of
    Vertex { process = Right proc } : _ -> isDelayProcess proc
    Vertex { process = Left var } : _ ->
      any isDelayProcess . filter (\Process { binder } -> binder == pure var) $ procs <> processes
    _ -> False
  isDelayProcess Process { body } =
    case collectArgs body of
      (Var func, _args) -> getOccString func == "delay"
      _ -> False
  out =
    if length edges /= 0 -- also ensures that minVert and maxVert is defined
      then
        pure $
          System
            { inputs
            , outputs
            , processes
            , vertices
            , edges
            , graph = Just graph
            }
      else Nothing

getProcesses :: [Process] -> CoreExpr -> [Process]
getProcesses acc = \case
  Lam _ e -> getProcesses acc e
  Let bind expr -> case makeProcess acc (Right bind) of
    Nothing -> getProcesses acc expr
    Just proc -> getProcesses (proc : acc) expr
  Case (Var _) _ _ (Alt (DataAlt dc) _ e : _) | isTupleDataCon dc ->
    getProcesses acc e
  -- Function composition
  App (App (App (App (App (Var v) _) _) _) e1) e2 | "." == (getOccString . getName) v ->
    let procs = getProcesses acc e1
     in getProcesses procs e2
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
    if typeOrConstraint a
      then getSignals bindacc inputAcc acc e
      else getSignals (a : bindacc) inputAcc acc e
  -- Add any top-level deconstructed input tuple mapping
  Case (Var v) _ _ (Alt (DataAlt dc) b e : _) | elem v bindacc && isTupleDataCon dc ->
    getSignals (b <> bindacc) ((v, b) : inputAcc) acc e
  Var v -> (bindacc, inputAcc, acc, [v])
  -- NOTE: should verify that the function is tuple
  e ->
    let (_, args) = collectArgs e
        argvars =
          mapMaybe
            ( \case
                Var v | typeOrConstraint v -> Nothing
                Var v | otherwise -> Just v
                Type _ -> Nothing
                _ -> Nothing
            )
            args
     in (bindacc, inputAcc, acc, argvars)
  where
    isSignal = (0 ==) . length . fst . extractTypes [] . varType . fst

-- | Resolve an application to a process, inputs and (potentially tupled) output
getApplication ::
  [CoreBndr] ->
  (CoreBndr, CoreExpr) ->
  (CoreExpr, [Var], Var, Maybe Var)
getApplication binds (output, expr) = (proc, input, output, splitTuples)
 where
  (input, splitTuples, proc) = stripApps ([], Nothing) expr
  stripApps (inputs, split) = \case
    App e (Var arg)
      | elem arg binds ->
          stripApps (arg : inputs, split) e
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

makeVertex :: [Process] -> Int -> (CoreExpr, [Var], [Var]) -> Maybe Vertex
makeVertex procs i = \case
  -- An application of a non-inline process
  (Var bind, inputs, outputs) ->
    Just $ Vertex
      { id = i
      , process = Left bind
      , inputs
      , outputs
      }
  -- Function composition
  -- (App (App (App (App (App (Var v) _) _) _) e1) e2, inputs, outputs) | "." == (getOccString . getName) v ->
  --   undefined
  -- An application of an inline process definition
  (expr, inputs, outputs) -> do
    process <- liftM Right $ makeProcess procs (Left (expr, inputs, outputs))
    pure $ Vertex
      { id = i
      , process
      , inputs
      , outputs
      }

makeEdge :: [Vertex] -> CoreBndr -> [Edge]
makeEdge vertices bind = [Edge bind] <*> source <*> targets
 where
  source = [i | Vertex{id = i, outputs} <- vertices, bind `elem` outputs]
  targets = [i | Vertex{id = i, inputs} <- vertices, bind `elem` inputs]
