{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedRecordDot #-}

module IR
  ( System (..)
  , Process (..)
  , Vertex (..)
  , Edge (..)
  , Port (..)
  , translate
  )
where

import Data.List (sort)
import Data.Maybe (mapMaybe)
import GHC.Core
import GHC.Core.Type
import GHC.Types.Var (isCoVar)
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Utils.Outputable (showPprUnsafe)

data System = System
  { inputs :: [Var]
  , outputs :: [Var]
  , processes :: [Process]
  , vertices :: [Vertex]
  , edges :: [Edge]
  }
instance  Show System where
  show System { .. } =
    "System(inputs = " <> showPprUnsafe inputs
    <> ", outputs = " <> showPprUnsafe outputs
    <> ", " <> (unlines . map ("\t" <>) . lines . concat . map (("\n" <>) . show) $ processes)
    <> ", " <> (unlines . map ("\t" <>) . lines . concat $ map (("\n" <>) . show) $ vertices)
    <> ", " <> (unlines . map ("\t" <>) . lines . concat $ map (("\n" <>) . show) $ edges)
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
  show Process { .. } =
    "Process(" <> showPprUnsafe binder
      <> ", inports = " <> show inports
      <> ", outports = " <> show outports
      <> ", " <> maybe ("{" <> showPprUnsafe body <> "}") show subsystem
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
  show Vertex { id = i, .. } =
    "Vertex(" <> show i
    <> ", inputs = " <> showPprUnsafe inputs
    <> ", outputs = " <> showPprUnsafe outputs
    <> ", " <> either showPprUnsafe show process
    <> ")"

-- An edge (signal) inside a system.
-- Can only refer to local vertices.
data Edge = Edge
  { binder :: !Var
  , source :: !Int
  , target :: !Int
  }
instance Show Edge where
  show Edge { .. } =
    "Edge(" <> showPprUnsafe binder
    <> ", " <> show source
    <> ", " <> show target
    <> ")"

data Port = Port
  { ty :: Type
  }
instance Show Port where
  show Port { .. } =
    "Port(" <> showPprUnsafe ty <> ")"

translate :: CoreProgram -> System
translate f =
  System
  { inputs = []
  , outputs = []
  , processes
  , vertices = []
  , edges = []
  }
  where
    processes = mapMaybe makeProcess $ f

makePorts :: ([Type], [Type]) -> ([Port], [Port])
makePorts (inty, outty) =
  (inports, outports)
  where
    inports = map Port inty
    outports = map Port outty

-- | Extract all arguments and returns
-- If the last return is a tuple type application, return the application list
extractTypes :: [Type] -> Type -> ([Type], [Type])
extractTypes acc = \case
  ForAllTy _ ty -> extractTypes acc ty
  FunTy { ft_arg = arg, ft_res = res } ->
    extractTypes (arg : acc) res
  t -> (reverse acc, extractConstructor [] t)
  where
    extractConstructor resacc = \case
      TyConApp v types | isTupleTyCon v -> reverse resacc <> types
      t -> reverse (t : resacc)

-- | Make a process from a binding.
-- A process should be self-contained, i.e. not have any communication outside
-- of its arguments and return.
makeProcess :: CoreBind -> Maybe Process
makeProcess (Rec _) = Nothing -- disallow non-self-contained processes
makeProcess (NonRec bind expr) =
  -- A process needs both an input and an output. A function with just an
  -- output is a value
  if length inports /= 0 && length outports /= 0
    then
      Just
        Process
          { binder = Just bind,
            inports,
            outports,
            subsystem = translateExpr expr,
            body = expr
          }
    else Nothing
  where
    (inports, outports) = makePorts . extractTypes [] $ varType bind

translateExpr :: CoreExpr -> Maybe System
translateExpr expr' = out
  where
    (_, inputs, expr) = collectTyAndValBinders expr'
    (binds, sigs, outputs) = getSignals inputs [] expr
    apps' = map (getApplication binds) sigs
    apps = mapMaybe (resolveTuples apps') apps'
    processes = getProcesses [] expr
    vertices = zipWith makeVertex [0..] apps
    edges = mconcat . map (makeEdge vertices) $ binds
    out =
      if length sigs /= 0
        then pure $ System
          { inputs
          , outputs
          , processes
          , vertices
          , edges
          }
        else Nothing

getProcesses :: [Process] -> CoreExpr -> [Process]
getProcesses acc = \case
  Lam _ e -> getProcesses acc e
  Let bind expr -> case makeProcess bind of
    Nothing -> getProcesses acc expr
    Just proc -> getProcesses (proc : acc) expr
  _ -> acc

-- | Get the applied signals of a subsystem
-- These will later be used to derive vertices and edges
getSignals ::
  [CoreBndr] ->
  [(CoreBndr, CoreExpr)] ->
  CoreExpr ->
  ([CoreBndr], [(CoreBndr, CoreExpr)], [CoreBndr])
getSignals bindacc acc = \case
  -- A signal should be fully applied, i.e. it should not have any input argument
  Let (NonRec b e) inExpr | length (fst $ extractTypes [] $ varType b) == 0
    -> getSignals (b : bindacc) ((b, e) : acc) inExpr
  -- Likely a process, handled separately
  Let (NonRec _ _) inExpr | otherwise
    -> getSignals bindacc acc inExpr
  -- A Rec binding should not contain any process since they are supposed to be
  -- self-contained. Therefore filter binds with inputs.
  Let (Rec sigs) inExpr
    -> let sigs' = filter ((0==) . length . fst . extractTypes [] . varType . fst) sigs
           b = map fst sigs'
        in getSignals (b <> bindacc) (sigs' <> acc) inExpr
  Lam a e ->
    getSignals (a : bindacc) acc e
  Var v -> (v : bindacc, acc, [v])
  -- NOTE: should verify that the function is tuple
  e -> let (_, args) = collectArgs e
           argvars = mapMaybe (\case
             Var v | isCoVar v -> Nothing
             Var v | otherwise -> Just v
             Type _ -> Nothing
             _ -> Nothing
             ) args
        in (argvars <> bindacc, acc, argvars)

-- | Resolve an application to a process, inputs and (potentially tupled) output
getApplication ::
  [CoreBndr] ->
  (CoreBndr, CoreExpr) ->
  (CoreExpr, [Var], Var, Maybe Var)
getApplication binds (output, expr) = (proc, input, output, splitTuples)
  where
    (input, splitTuples, proc) = stripApps ([], Nothing) expr
    stripApps (inputs, split) = \case
      App e (Var arg) | any (\bind -> bind == arg) binds ->
        stripApps (arg : inputs, split) e
      e@(Case (Var arg) _b _t ((Alt _ _ _e) : _)) | any (\bind -> bind == arg) binds ->
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
    splits = mapMaybe (\(p, _, out, tup) ->
      case tup of
        Just tuple | output == tuple -> Just (p, out)
        _ -> Nothing
      ) apps
    outputs' = map snd . sort . mapMaybe getPos $ splits
    outputs = if length outputs' /= 0 then outputs' else [output]
    getPos :: (CoreExpr, Var) -> Maybe (Int, Var)
    getPos (expr, var) = case expr of
      (Case _ _ _ ((Alt _ args (Var out)) : _)) ->
        lookup out (zip args (zip [0..] $ repeat var))
      _ -> Nothing

makeVertex :: Int -> (CoreExpr, [Var], [Var]) -> Vertex
makeVertex i = \case
  -- An application of a non-inline process
  (Var bind, inputs, outputs) ->
      Vertex
      { id = i
      , process = Left bind
      , inputs
      , outputs
      }
  -- An application of an inline process definition
  (expr, inputs, outputs) ->
    Vertex
    { id = i
    , process = Right $
        Process
        { binder = Nothing
        , inports = map (Port . varType) inputs
        , outports = map (Port . varType) outputs
        , subsystem = translateExpr expr
        , body = expr
        }
    , inputs
    , outputs
    }

makeEdge :: [Vertex] -> CoreBndr -> [Edge]
makeEdge vertices bind = [Edge bind] <*> source <*> targets
  where
    source = [i | Vertex { id = i, outputs } <- vertices, bind `elem` outputs]
    targets = [i | Vertex { id = i, inputs } <- vertices, bind `elem` inputs]
