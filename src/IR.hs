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
  , functions :: [CoreBind]
  }
instance  Show System where
  show System { id = i, .. } =
    "System("
    <> show i
    <> ", " <> (intercalate "\n" $ map show vertices)
    <> ", " <> show edges
    <> ", " <> showPprUnsafe functions
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
      <> ", " <> showPprUnsafe ty
      <> ", {" <> showPprUnsafe function <> "}"
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
  , functions = []
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

extractTypes :: [Type] -> Type -> ([Type], [Type])
extractTypes acc = \case
  FunTy { ft_arg = arg, ft_res = res } ->
    extractTypes (arg : acc) res
  t -> (reverse acc, extractConstructor [] t)
  where
    extractConstructor resacc = \case
      (TyConApp _ types) -> types
      (AppTy t1 t2) -> extractConstructor (t1 : resacc) t2
      t -> (t : resacc)

makeVertex :: CoreBind -> Vertex
makeVertex (Rec _) = undefined
makeVertex (NonRec bind expr) =
  Vertex
    { id = varUnique bind
    , binder = bind
    , inputs = inports
    , outputs = outports
    , subsystem = Nothing
    , function = expr
    , ty = varType bind
    }
  where
    (inports, outports) = makePorts . extractTypes [] $ varType bind
