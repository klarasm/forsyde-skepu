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

--import Data.List (intercalate, sort)
import Data.List (sort)
import Data.Maybe (mapMaybe)
import GHC.Core
import GHC.Core.Type
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Types.Unique (Unique)
import GHC.Types.Var (varUnique)
import GHC.Types.Name (isTupleTyConName)
import GHC.Utils.Outputable (showPprUnsafe)

data Id
  = None
  | Unique Unique
  | Assigned Int
  deriving (Show)

data System = System
  { id :: Id
  , inputs :: [Var]
  , outputs :: [Var]
  , processes :: [Process]
  , vertices :: [Vertex]
  , edges :: [Edge]
  }
instance  Show System where
  show System { id = i, .. } =
    "System("
    <> show i
    <> ", inputs = " <> showPprUnsafe inputs
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
    "Process("
      <> showPprUnsafe binder
      <> ", inports = " <> show inports
      <> ", outports = " <> show outports
      <> ", " <> show subsystem
      -- <> ", {" <> showPprUnsafe body <> "}"
      <> ")"

-- A process connected in a network.
-- It must therefore have at least an input and an output
data Vertex = Vertex
  { id :: Id
  , process :: Either Var Process
  , inputs :: [Var]
  , outputs :: [Var]
  }
instance Show Vertex where
  show Vertex { id = i, .. } =
    "Vertex("
    <> show i
    <> ", " <> either showPprUnsafe show process
    <> ", inputs = " <> showPprUnsafe inputs
    <> ", outputs = " <> showPprUnsafe outputs
    <> ")"

data Edge = Edge
  { binder :: !Var
  , source :: !Id
  , target :: !Id
  }
instance Show Edge where
  show Edge { .. } =
    "Edge("
    <> showPprUnsafe binder
    <> ", " <> show source
    <> ", " <> show target
    <> ")"

data Port = Port
  { ty :: Type
  }
instance Show Port where
  show Port { .. } =
    "Port("
    <> showPprUnsafe ty
    <> ")"

translate :: CoreProgram -> System
translate f =
  System
  { id = None
  , inputs = []
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
      TyConApp v types | isTupleTyConName $ tyConName v -> reverse resacc <> types
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
            subsystem = translateExpr (Just bind) expr,
            body = expr
          }
    else Nothing
  where
    (inports, outports) = makePorts . extractTypes [] $ varType bind

translateExpr :: Maybe CoreBndr -> CoreExpr -> Maybe System
translateExpr bind expr' = out
  where
    (_, inputs, expr) = collectTyAndValBinders expr'
    (binds, sigs, outputs) = getSignals inputs [] expr
    apps' = map (getApplication binds sigs) sigs
    apps = mapMaybe (resolveTuples apps') apps'
    processes = getProcesses [] expr
    vertices = map makeVertex apps
    out =
      if length sigs /= 0
        then pure $ System
          { id = maybe None (Unique . varUnique) bind
          , inputs
          , outputs
          , processes
          , vertices
          , edges = []
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
-- getSignals bindacc acc expr = case collectBinders expr of
getSignals bindacc acc = \case
  -- A signal should be fully applied, i.e. it should not have any input argument
  Let (NonRec b e) inExpr | length (fst $ extractTypes [] $ varType b) == 0
    -> getSignals bindacc ((b, e) : acc) inExpr
  -- Likely a process, handled separately
  Let (NonRec _ _) inExpr | otherwise
    -> getSignals bindacc acc inExpr
  -- A Rec binding should not contain any process since they are supposed to be
  -- self-contained. Therefore filter binds with inputs.
  Let (Rec sigs) inExpr
    -> getSignals bindacc ((filter ((0==) . length . fst . extractTypes [] . varType . fst) sigs) <> acc) inExpr
  Lam a e ->
    getSignals (a : bindacc) acc e
  -- NOTE: need to handle system output somehow
  _ -> (bindacc, acc, [])

-- | Resolve an application to a process, inputs and (potentially tupled) output
getApplication ::
  [CoreBndr] ->
  [(CoreBndr, CoreExpr)] ->
  (CoreBndr, CoreExpr) ->
  (CoreExpr, [Var], Var, Maybe Var)
getApplication binds allSigs (output, expr) = (proc, input, output, splitTuples)
  where
    (input, splitTuples, proc) = stripApps ([], Nothing) expr
    stripApps (inputs, split) = \case
      App e (Var arg)
        | any (\(sig, _) -> sig == arg) allSigs || any (\bind -> bind == arg) binds ->
        stripApps (arg : inputs, split) e
      e@(Case (Var arg) _b _t ((Alt _ _ _e) : _))
        | any (\(sig, _) -> sig == arg) allSigs || any (\bind -> bind == arg) binds ->
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

makeVertex :: (CoreExpr, [Var], [Var]) -> Vertex
makeVertex = \case
  -- An application of a non-inline process
  (Var bind, inputs, outputs) ->
      Vertex
      { id = None
      , process = Left bind
      , inputs
      , outputs
      }
  -- An application of an inline process definition
  (expr, inputs, outputs) ->
    Vertex
    { id = None
    , process = Right $
        Process
        { binder = Nothing
        , inports = map (Port . varType) inputs
        , outports = map (Port . varType) outputs
        , subsystem = translateExpr Nothing expr
        , body = expr
        }
    , inputs
    , outputs
    }
