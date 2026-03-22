{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedRecordDot #-}

module IR
  ( System (..)
  , Vertex (..)
  , Edge (..)
  , Port (..)
  , translate
  )
where

import Data.List (intercalate)
import GHC.Core
import GHC.Core.Type
import GHC.Core.TyCo.Rep
import GHC.Types.Unique (Unique)
import GHC.Types.Var (varUnique)
import GHC.Utils.Outputable (showPprUnsafe)

type Id = Unique

data System = System
  { id :: Maybe Id
  , vertices :: [Vertex]
  , edges :: [Edge]
  -- , sigs :: [(CoreBndr, CoreExpr)]
  , apps :: [(CoreExpr, [Id], Id)]
  }
instance  Show System where
  show System { id = i, .. } =
    "System("
    <> show i
    <> ", " <> (intercalate "\n" $ map show vertices)
    <> ", " <> show edges
    -- <> ", " <> "{" <> intercalate ", " (map (\(a, _) -> (showPprUnsafe a)) sigs) <> "}"
    <> ", " <> "{" <> intercalate ", " (map (\(a, b, c) -> "(" <> (showPprUnsafe a) <> ", " <> (showPprUnsafe b) <> ", " <> (showPprUnsafe c) <> ")") apps) <> "}"
    <> ")"

data Vertex = Vertex
  { id :: !Id
  , binder :: CoreBndr
  , inputs :: [Port]
  , outputs :: [Port]
  , subsystem :: Maybe System
  , function :: CoreExpr
  , ty :: Type
  }
instance Show Vertex where
  show Vertex {id = i, ..} =
    "Vertex("
      <> show i
      <> ", " <> showPprUnsafe binder
      <> ", inputs = " <> show inputs
      <> ", outputs = " <> show outputs
      <> ", " <> show subsystem
      -- <> ", " <> showPprUnsafe ty
      -- <> ", {" <> showPprUnsafe function <> "}"
      <> ")"

data Edge = Edge
  { id :: !Id
  , source :: !Id
  , target :: !Id
  }
  deriving (Show)

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
  { id = Nothing
  , vertices
  , edges = []
  -- , sigs = []
  , apps = []
  }
  where
    vertices = filter nonemptyVertex . map makeVertex $ f
    -- We only care about actual functions
    nonemptyVertex Vertex { inputs, outputs } =
      length inputs /= 0 || length outputs /= 0

makePorts :: ([Type], [Type]) -> ([Port], [Port])
makePorts (inty, outty) =
  (inports, outports)
  where
    inports = map Port inty
    outports = map Port outty

-- | Extract all arguments and returns
-- If the last return is a type application, return the application list
extractTypes :: [Type] -> Type -> ([Type], [Type])
extractTypes acc = \case
  ForAllTy _ ty -> extractTypes acc ty
  FunTy { ft_arg = arg, ft_res = res } ->
    extractTypes (arg : acc) res
  t -> (reverse acc, extractConstructor [] t)
  where
    extractConstructor resacc = \case
      TyConApp _ types -> reverse resacc <> types
      AppTy t1 t2 -> extractConstructor (t1 : resacc) t2
      t -> reverse (t : resacc)

makeVertex :: CoreBind -> Vertex
makeVertex (Rec _) = undefined
makeVertex (NonRec bind expr) =
  Vertex
    { id = varUnique bind
    , binder = bind
    , inputs = inports
    , outputs = outports
    , subsystem = translateExpr bind expr
    , function = expr
    , ty = varType bind
    }
  where
    (inports, outports) = makePorts . extractTypes [] $ varType bind

translateExpr :: CoreBndr -> CoreExpr -> Maybe System
translateExpr bind expr = out
  where
    -- (vertices, edges) = translateExpr' ([], []) expr
    (binds, sigs) = getSignals [] [] expr
    apps = map (getApplication binds sigs) sigs
    out =
      if length sigs /= 0
        then pure $ System {id = Just $ varUnique bind, vertices = [], edges = [], apps }
        else Nothing

-- translateExpr' :: ([Vertex], [Edge]) -> CoreExpr -> ([Vertex], [Edge])
-- translateExpr' acc expr = case collectBinders expr of
--   (binds, Var v) -> acc
--   (binds, Lit l) -> acc
--   (binds, App b a) -> acc
--   (binds, Lam a e) -> acc
--   (binds, Let b e) -> acc
--   (binds, Case e b t alts) -> acc
--   (binds, Cast _ _) -> acc
--   (binds, Tick _ e) -> acc
--   (binds, Type t) -> acc
--   (binds, Coercion _) -> acc

-- | Get the applied signals of a subsystem
-- These will later be used to derive vertices and edges
getSignals ::
  [CoreBndr] ->
  [(CoreBndr, CoreExpr)] ->
  CoreExpr ->
  ([CoreBndr], [(CoreBndr, CoreExpr)])
getSignals bindacc acc expr = case collectBinders expr of
  (newbind, Let (NonRec b e) inExpr) -> getSignals (newbind <> bindacc) ((b, e) : acc) inExpr
  (newbind, Let (Rec sigs) inExpr) -> getSignals (newbind <> bindacc) (sigs <> acc) inExpr
  _ -> (bindacc, acc)

-- | Resolve an application to a process, inputs and (potentially tupled) output
getApplication ::
  [CoreBndr] ->
  [(CoreBndr, CoreExpr)] ->
  (CoreBndr, CoreExpr) ->
  (CoreExpr, [Id], Id)
getApplication binds allSigs (output, expr) = (proc, input, varUnique output)
  where
    (input, proc) = stripApps [] expr
    stripApps inputs = \case
      App e (Var arg) | any (\(sig, _) -> sig == arg) allSigs || any (\bind -> bind == arg) binds ->
        stripApps (varUnique arg : inputs) e
      e -> (inputs, e)
