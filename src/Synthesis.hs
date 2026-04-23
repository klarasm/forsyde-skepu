{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module Synthesis (
  Context (..),
  Synthesizable (..),
) where

import GHC.Core
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Types.Literal
import GHC.Types.Name (getOccString)
import GHC.Utils.Outputable (showPprUnsafe)

import qualified CIR
import Data.List (find)
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import IR
import Prettyprinter

data IdExt
  = Name String
  | Input
  | Output
  | Tmp
  | IVector
  | IMatrix
  | IEmpty
  | Reduce
  | Map
  deriving (Eq, Ord, Show)

instance Pretty IdExt where
  pretty (Name s) = pretty s
  pretty Input = pretty "input"
  pretty Output = pretty "output"
  pretty Tmp = pretty "tmp"
  pretty IVector = pretty "skepu::Vector"
  pretty IMatrix = pretty "skepu::Matrix"
  pretty IEmpty = mempty
  pretty Reduce = pretty "skepu::Reduce"
  pretty Map = pretty "skepu::Map"

type CType = CIR.Type IdExt
type CExpression = CIR.Expression IdExt
type CStatement = CIR.Statement IdExt
type CProgram = CIR.Program IdExt

data (Show a) => Context a = Context
  { from :: Id ()
  , ret :: CType
  , inputs :: [(CType, Id IdExt)]
  , outputs :: [(CType, Id IdExt)]
  , delayStorage :: S.Set (CType, Id IdExt, CExpression)
  , body :: CStatement
  }
  deriving (Show)
instance (Show a, Pretty a) => Pretty (Context a) where
  pretty Context{..} =
    pretty "Context"
      <> (nest 4 . tupled)
        [ pretty from
        , pretty ret
        , pretty inputs
        , pretty outputs
        , pretty . S.elems $ delayStorage
        , pretty body
        ]

class Synthesizable a where
  -- may need to resolve a previously unresolved process as dependency
  synthesize :: [a] -> a -> ([Context a], [Context a]) -> ([Context a], [Context a])
  compose :: ([Context a], [Context a]) -> CProgram

portToC :: Port -> CType
portToC = \case
  Signal a _ _ -> CIR.TPointer $ portToC a
  AbstExt a _ -> portToC a
  Vector (Vector p _) _ ->
    CIR.TConstructor (CIR.TIdent $ ExId IMatrix) (portToC p)
  Vector p _ ->
    CIR.TConstructor (CIR.TIdent $ ExId IVector) (portToC p)
  Opaque t -> typeToCType t

typeToCType :: Type -> CType
typeToCType = \case
  TyVarTy v
    | getOccString v == "Int" -> CIR.TInt
    | getOccString v == "Integer" -> CIR.TInt
    | getOccString v == "Float" -> CIR.TFloat
    | getOccString v == "Double" -> CIR.TFloat
  TyVarTy v -> error $ "TyVarTy: " <> showPprUnsafe v
  TyConApp v []
    | getOccString v == "Int" -> CIR.TInt
    | getOccString v == "Integer" -> CIR.TInt
    | getOccString v == "Float" -> CIR.TFloat
    | getOccString v == "Double" -> CIR.TFloat
  TyConApp v1 [v2] | getOccString v1 == "Num" -> case v2 of
    TyVarTy v2'
      | getOccString v2' == "Integer" -> CIR.TInt
      | getOccString v2' == "Int" -> CIR.TInt
      | getOccString v2' == "Float" -> CIR.TFloat
      | getOccString v2' == "Double" -> CIR.TFloat
    TyConApp v2' _
      | getOccString v2' == "Integer" -> CIR.TInt
      | getOccString v2' == "Int" -> CIR.TInt
      | getOccString v2' == "Float" -> CIR.TFloat
      | getOccString v2' == "Double" -> CIR.TFloat
    TyConApp v2' _ -> error . showPprUnsafe $ v2'
    _ -> error . showPprUnsafe $ v2
  TyConApp v1 _ | getOccString v1 == "Floating" -> CIR.TFloat
  TyConApp v1 _ | getOccString v1 == "Integral" -> CIR.TInt
  TyConApp v a -> error $ "TyConApp: " <> (getOccString . tyConName) v <> " " <> showPprUnsafe a
  t -> error $ "Something else: " <> showPprUnsafe t

exprToCType :: CoreExpr -> CType
exprToCType = \case
  Type t -> portToC . makePort $ t
  Var v -> portToC . makePort . varType $ v
  _ -> error "Not a type!"

varToCDef :: Var -> (CType, Id IdExt)
varToCDef v =
  let port = makePort . varType $ v
      ty = portToC port
      name = Direct v
   in (ty, name)

getDelayExpr :: CoreExpr -> Maybe CoreExpr
getDelayExpr = \case
  App (App (Var v) _) e | isDelayVar v -> Just e
  _ -> Nothing

delayExprToC :: CoreExpr -> CExpression
delayExprToC = \case
  App (Var _) (Lit (LitNumber _ i)) -> CIR.EInt . fromIntegral $ i
  _ -> undefined

inputIds :: [Id IdExt]
inputIds = map ((ExId Input <>) . Ix) [0 ..]
inputArgs :: [CExpression]
inputArgs = map CIR.EVar inputIds
outputIds :: [Id IdExt]
outputIds = map ((ExId Output <>) . Ix) [0 ..]
outputArgs :: [CExpression]
outputArgs = map CIR.EVar outputIds

vertexToExpr :: (Foldable t) => t Var -> [Context a] -> Vertex -> CExpression
vertexToExpr pointers context Vertex{id = _, ..} = case process of
  Right _ -> undefined
  Left v -> CIR.ECall (const IEmpty <$> v) $ map ioToExpr inputs <> map ioToExpr outputs <> (delayParams v)
 where
  delayParams v =
    S.elems
      . S.map (\(_, s, _) -> CIR.EVar s)
      . mconcat
      . map (\Context{delayStorage} -> delayStorage)
      . filter (\Context{from} -> v == from)
      $ context
  ioToExpr io =
    if elem io pointers
      then CIR.EVar $ Direct io
      else CIR.EReference . CIR.EVar $ Direct io

mkTemp :: Int -> (Int, Id IdExt)
mkTemp ix = (ix + 1, ExId Tmp <> Ix ix)

data OutputLoc
  = FunArg
  | Return

skelToSkePU :: String -> Maybe (OutputLoc, Id IdExt)
skelToSkePU = \case
  "reduce" -> Just (Return, ExId Reduce)
  "farm11" -> Just (FunArg, ExId Map <> (ExId $ Name "<1>"))
  "farm12" -> Just (FunArg, ExId Map <> (ExId $ Name "<1>"))
  "farm21" -> Just (FunArg, ExId Map <> (ExId $ Name "<2>"))
  "farm22" -> Just (FunArg, ExId Map <> (ExId $ Name "<2>"))
  _ -> Nothing

resolveBinOp ::
  Int ->
  [CStatement] ->
  (CType, CExpression) ->
  (CType, CExpression) ->
  CType ->
  String ->
  (Int, [CStatement], (CType, CExpression))
resolveBinOp tmpix stmts (t1, expr1) (t2, expr2) tout = \case
  "+" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Add e1 e2))
  "*" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Multiply e1 e2))
  "-" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Subtract e1 e2))
  "quot" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "/" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "div" -> error "Haskell `div` rounds to negative infinity, not implemented. Consider using `quot`"
  u -> error $ "Unknown function: " <> u
 where
  e1 = derefArg (needDeref 0 (t1, tout)) expr1
  e2 = derefArg (needDeref 0 (t2, tout)) expr2

-- varToArg :: (Eq a) => [a] -> a -> Maybe CExpression
varToArg :: [CType] -> [Var] -> Var -> Maybe (CType, CIR.Expression IdExt)
varToArg tin args v =
  toExpr
    <$> find (\(_, v', _) -> v' == v) (zip3 [0 ..] args tin)
 where
  toExpr (ix, _, t) = (t, CIR.EVar $ ExId Input <> Ix ix)

exprToLambda :: Int -> OutputLoc -> [Var] -> [CType] -> CType -> [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToLambda tmpix outLoc args tin tout inports outports expr = case expr of
  -- A function passed as a value (with type constraints). Construct a lambda
  App (App (Var f) t1) t2
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        case makePorts . extractTypes [] . varType $ f of
          (a1 : a2 : [], out : []) ->
            let in1 = ExId Input <> Ix 0
                t1' = exprToCType t1
                in2 = ExId Input <> Ix 1
                t2' = exprToCType t2
                (tmpix', stmts, (_, expr')) = resolveBinOp tmpix [] (t1', CIR.EVar in1) (t2', CIR.EVar in2) tout (getOccString f)
                expr'' = CIR.ELambda [] [(t1', in1), (t2', in2)] $ CIR.SScope [CIR.SReturn . Just $ expr']
             in (tmpix', stmts, (tout, expr''))
          _ -> undefined
  App (App (App (Var f) t1) t2) v1@(Var v)
    | typeOrConstraint t1 && typeOrConstraint t2 && (not $ typeOrConstraint v1) ->
        case (makePorts . extractTypes [] . varType $ f, varToArg tin args v) of
          -- A partially applied binary function, construct a lambda. Note that
          -- SkePU does not use variable capture, but instead passes it as a
          -- scalar.
          ((a1 : a2 : [], out : []), Just (argty1, arg1)) ->
            let in1 = ExId Input <> Ix 0
                t1' = exprToCType t1
                in2 = ExId Input <> Ix 1
                t2' = exprToCType t2
                (tmpix', stmts, (_, expr')) = resolveBinOp tmpix [] (t1', CIR.EVar in1) (t2', CIR.EVar in2) tout (getOccString f)
                expr'' = CIR.ELambda [] [(t1', in1), (t2', in2)] $ CIR.SScope [CIR.SReturn . Just $ expr']
             in (tmpix', stmts, (tout, expr''))
          _ -> undefined
  e ->
    let (tmpix1, stmts1, (_, expr1)) = exprToCExpr tmpix outLoc args tin tout inputs outports e
        inputs = zip tin inputIds
        expr2 = CIR.ELambda [] inputs $ CIR.SScope [CIR.SReturn $ Just expr1]
     in (tmpix1, stmts1, (tout, expr2))

exprToCExpr :: Int -> OutputLoc -> [Var] -> [CType] -> CType -> [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToCExpr tmpix outLoc args tin tout inports outports expr = case expr of
  -- Inner function applied to a function and a var
  App (App (App (App (Var inner) t1) t2) e1) e2@(Var v)
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        case skelToSkePU $ getOccString inner of
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args [exprToCType t1, exprToCType t2] tout inports outports e1
                (tmpix2, outname) = mkTemp tmpix1
                (tmpix3, skelInstance) = mkTemp tmpix2
                inputs = map CIR.EDereference . zipWith const inputArgs $ tin
                stmts =
                  [ CIR.SVarDecl tout outname
                  , CIR.SVarDef CIR.TAuto skelInstance $ CIR.ECall skel [e1']
                  , CIR.SExpr $
                      CIR.ECall skelInstance $
                        [CIR.EVar outname] <> inputs
                  ]
             in (tmpix3, stmts1 <> stmts, (tout, CIR.EVar outname))
          Nothing ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix FunArg args tin (exprToCType t1) inports outports e1
                (tmpix2, stmts2, (t2', expr2)) = exprToCExpr tmpix1 FunArg args tin (exprToCType t2) inports outports e2
             in resolveBinOp tmpix2 (stmts1 <> stmts2) (t1', expr1) (t2', expr2) tout $ getOccString inner
  -- Binary operator/function (with type variables)
  App (App (App (App (Var f) t1) t2) e1) e2
    | typeOrConstraint t1 && typeOrConstraint t2 && (not $ typeOrConstraint e1) && (not $ typeOrConstraint e2) ->
        let (tmpix1, stmts1, (_, expr1)) = exprToCExpr tmpix FunArg args tin (exprToCType t1) inports outports e1
            (tmpix2, stmts2, (_, expr2)) = exprToCExpr tmpix1 FunArg args tin (exprToCType t2) inports outports e2
         in resolveBinOp tmpix2 (stmts1 <> stmts2) (exprToCType t1, expr1) (exprToCType t2, expr2) tout $ getOccString f
  App (App (App (App (Var f) t1) t2) t3) e1
    | typeOrConstraint t1 && typeOrConstraint t2 && typeOrConstraint t3 && (not $ typeOrConstraint e1) ->
        case skelToSkePU (getOccString f) of
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args (map exprToCType [t1, t2]) (exprToCType t3) inports outports e1
                (tmpix2, outname) = mkTemp tmpix1
                (tmpix3, skelInstance) = mkTemp tmpix2
                inputs = map CIR.EDereference . zipWith const inputArgs $ tin
                stmts =
                  [ CIR.SVarDecl tout outname
                  , CIR.SVarDef CIR.TAuto skelInstance $ CIR.ECall skel [e1']
                  , CIR.SExpr $
                      CIR.ECall skelInstance $
                        [CIR.EVar outname] <> inputs
                  ]
             in (tmpix3, stmts1 <> stmts, (tout, CIR.EVar outname))
          Nothing -> undefined
  -- A partially applied binary operator passed as a value. Apply it to the input argument
  App (App (App (Var f) t1) t2) e
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        let (tmpix1, stmts1, (t1', e1)) = exprToCExpr tmpix FunArg args tin tout inports outports e
            v1 = derefArg (needDeref 0 (fst . head $ inports, exprToCType t1)) $ CIR.EVar $ ExId Input <> Ix 0
         in resolveBinOp tmpix1 stmts1 (t1', e1) (head tin, v1) tout $ getOccString f
  -- Unary operator/function (with type variables)
  App (App (Var f) t) (Var v) | typeOrConstraint t && (not $ typeOrConstraint $ Var v) ->
    case varToArg tin args v of
      Just (argty, arg) ->
        (tmpix, [], (tout, CIR.ECall (Direct f) [arg]))
      Nothing -> error $ "Var not in args! " <> showPprUnsafe expr
  -- Inner function applied to a function. Apply it to the input arguments
  App (App (Var inner) t) e
    | typeOrConstraint t && (not $ typeOrConstraint e) ->
        case skelToSkePU $ getOccString inner of
          Nothing -> error $ "Unknown skeleton: " <> getOccString inner
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1)) = exprToLambda tmpix ret args tin tout inports outports e
                (tmpix2, outname) = mkTemp tmpix1
                (tmpix3, skelInstance) = mkTemp tmpix2
                inputs = map CIR.EDereference . zipWith const inputArgs $ tin
                call =
                  CIR.ECall skelInstance $
                    case ret of
                      FunArg -> [CIR.EVar outname] <> inputs
                      Return -> [CIR.EDereference $ CIR.EVar $ ExId Input <> Ix 0]
                stmts =
                  [ CIR.SVarDecl tout outname
                  , CIR.SVarDef CIR.TAuto skelInstance $ CIR.ECall skel [e1]
                  ]
                    <> case ret of
                      FunArg -> [CIR.SExpr call]
                      Return -> []
             in ( tmpix3
                , stmts1 <> stmts
                , case ret of
                    FunArg -> (tout, CIR.EVar outname)
                    Return -> (tout, call)
                )
  -- A binary operator passed as a value. Apply it to the input arguments
  App (App (Var f) t1) t2
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        let v1 = CIR.EDereference $ CIR.EVar $ ExId Input <> Ix 0
            v2 = CIR.EDereference $ CIR.EVar $ ExId Input <> Ix 1
         in resolveBinOp tmpix [] (head tin, v1) (head . tail $ tin, v2) tout $ getOccString f
  -- An integer literal
  App _ (Lit (LitNumber _ i)) -> (tmpix, [], (CIR.TInt, CIR.EInt $ fromIntegral i))
  Lit (LitNumber _ i) -> (tmpix, [], (CIR.TInt, CIR.EInt $ fromIntegral i))
  Var v -> case varToArg (map fst inports) args v of
    Just (t', v') -> (tmpix, [], (tout, derefArg (needDeref 0 (t', tout)) v'))
    -- Assume the Var is a function
    -- TODO: need to rethink multiple output
    Nothing ->
      let (inputs, outputs) = extractTypes [] . varType $ v
          (inPorts, outPorts) = makePorts . extractTypes [] . varType $ v
          deref = map (needDeref 0) . flip zip tin $ map (fst) inports
          inArgs = zipWith derefArg deref $ zipWith const inputArgs inputs
       in if length outputs == 1
            then
              ( tmpix
              , []
              , (portToC . head $ outPorts, CIR.ECall (Direct v) inArgs)
              )
            else error "user functions with multiple output is currently unsupported"
  e -> error . showPprUnsafe $ e

needDeref :: (Num t) => t -> (CIR.Type a1, CIR.Type a2) -> t
needDeref cur = \case
  (CIR.TPointer argTy, CIR.TPointer parmTy) -> needDeref cur (argTy, parmTy)
  (CIR.TPointer argTy, parmTy) -> needDeref (cur + 1) (argTy, parmTy)
  (argTy, CIR.TPointer parmTy) -> needDeref (cur - 1) (argTy, parmTy)
  _ -> cur

derefArg :: (Ord t, Num t) => t -> CIR.Expression a -> CIR.Expression a
derefArg num var = case compare num 0 of
  LT -> derefArg (num + 1) $ CIR.EReference var
  GT -> derefArg (num - 1) $ CIR.EDereference var
  EQ -> var

bodyToStatement :: [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (OutputLoc, CStatement)
bodyToStatement inports outports = \case
  App (App (App (App (App (App (App (App (App (Var v) _) _) _) _) _) _) _) _) e ->
    error $ "9App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (Var v) _) _) _) _) _) _) _) e ->
    error $ "8App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (Var v) _) _) _) _) _) _) e ->
    error $ "7App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (Var v) _) _) _) _) _) e ->
    error $ "6App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (Var v) t1) t2) t3) t4) e
    | getOccString v == "comb22" ->
        let (args, expr) = collectBinders e
         in case expr of
              App (App (App (App (Var v') te1) te2) e1) e2
                | getOccString v' == "(,)" ->
                    let tout1 = exprToCType te1
                        tout2 = exprToCType te2
                        (cntr, init1, (_, ea1)) = exprToCExpr 0 FunArg args (map exprToCType [t1, t2]) tout1 inports outports e1
                        (_, init2, (_, ea2)) = exprToCExpr cntr FunArg args (map exprToCType [t1, t2]) tout2 inports outports e2
                     in ( FunArg
                        , CIR.SScope $
                            init1
                              <> init2
                              <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1
                                 , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 1) ea2
                                 ]
                        )
              e' -> error . showPprUnsafe $ e'
    | otherwise ->
        error $ "5App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (Var v) t1) t2) t3) e
    | getOccString v == "comb21" ->
        let (args, expr) = collectBinders e
            (_, init1, (_, ea1)) = exprToCExpr 0 FunArg args (map exprToCType [t1, t2]) (exprToCType t3) inports outports expr
         in ( FunArg
            , CIR.SScope $
                init1
                  <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1
                     ]
            )
    | getOccString v == "comb12" ->
        let (args, expr) = collectBinders e
         in case expr of
              App (App (App (App (Var v') tout1) tout2) e1) e2
                | getOccString v' == "(,)" ->
                    let (cntr, init1, (_, ea1)) = exprToCExpr 0 FunArg args (map exprToCType [t1]) (exprToCType tout1) inports outports e1
                        (_, init2, (_, ea2)) = exprToCExpr cntr FunArg args (map exprToCType [t1]) (exprToCType tout2) inports outports e2
                     in ( FunArg
                        , CIR.SScope $
                            init1
                              <> init2
                              <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) $ ea1
                                 , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 1) $ ea2
                                 ]
                        )
              e' -> error . showPprUnsafe $ e'
    | otherwise ->
        error $ "4App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (Var v) t1) t2) e
    | getOccString v == "comb11" ->
        let (args, expr) = collectBinders e
            (_, init1, (_, ea1)) = exprToCExpr 0 FunArg args (map exprToCType [t1]) (exprToCType t2) inports outports expr
         in ( FunArg
            , CIR.SScope $
                init1
                  <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) $ ea1
                     ]
            )
    | otherwise ->
        error $ "3App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (Var v) _) e
    | getOccString v == "delay" ->
        ( FunArg
        , CIR.SScope
            [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) (CIR.EDereference . CIR.EVar $ ExId Input <> Ix 0)
            ]
        )
    | otherwise ->
        error $ "2App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (Var v) e ->
    error $ "1App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  -- Might be a regular function, i.e. not a process
  e@(Lam _ _) ->
    let (args, expr') = collectBinders e
        (_, stmts, (_, expr)) = exprToCExpr 0 Return args (map fst inports) (fst . head $ outports) inports outports expr'
        output = CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0
     in ( Return
        , CIR.SScope $
            stmts
              <> [CIR.SReturn . Just $ expr]
        )
  e -> error . showPprUnsafe $ e

removePoint :: CIR.Type a -> CIR.Type a
removePoint = \case
  CIR.TPointer t -> t
  t -> t

instance Synthesizable Process where
  synthesize procs p@Process{..} (newC, allC) =
    case filter (\Context{from} -> binder == from) allC of
      c : _ -> (c : newC, allC)
      _ ->
        case subsystem of
          Nothing ->
            let inputs = zip (map portToC inports) inputIds
                outputs = zip (map portToC outports) outputIds
                (retLoc, body') = bodyToStatement inputs outputs body
                context =
                  Context
                    { from = binder
                    , ret = case retLoc of
                        FunArg -> CIR.TVoid
                        Return -> fst . head $ outputs
                    , inputs
                    , outputs = case retLoc of
                        FunArg -> outputs
                        Return -> []
                    , delayStorage = mempty
                    , body = body'
                    }
             in (context : newC, context : allC)
          Just System{..} ->
            let procs' = filter (/= p) procs
                systemProcs = S.elems . mconcat . map (vertexProcs (S.fromList procs)) $ vertices
                (subsysNew, allC1) = foldr (synthesize procs') (newC, allC) systemProcs
                inDefs = map varToCDef inputs
                outDefs = map varToCDef outputs
                delays = mapMaybe (delayVertex procs) vertices
                delayProcs = mconcat . map (delayProc procs) $ delays
                delayBodies = sequence . map (getDelayExpr . \Process{body = b} -> b) $ delayProcs
                delayExprs = map delayExprToC <$> delayBodies
                delaySigs =
                  mconcat
                    . map
                      ( \v@Vertex{outputs = outputs'} ->
                          if length outputs == 1
                            then outputs'
                            else error $ "invalid delay outputs: " <> show v
                      )
                    $ delays
                delayTypes = map varToCDef delaySigs
                delayDefs = delayExprs >>= \_c -> Just $ ((\(a, b) c -> (a, b, c)) <$> delayTypes) <*> _c
                subsysStorage = mconcat . map (\Context{delayStorage} -> delayStorage) $ subsysNew
                findVert vid = find (\Vertex{id = i} -> i == vid) vertices
                schedVert = mapMaybe findVert <$> schedule
                pointers = delaySigs <> inputs <> outputs
                schedStmts = map (CIR.SExpr . vertexToExpr pointers subsysNew) <$> schedVert
                locals = filter (\v -> not (elem v pointers)) . map (\(Edge v _ _) -> v) $ edges
                localDefs = map ((\(t, s) -> CIR.SVarDecl t s) . (\(t, n) -> (removePoint t, n)) . varToCDef) locals
                context =
                  Context
                    { from = binder
                    , ret = CIR.TVoid
                    , inputs = inDefs
                    , outputs = outDefs
                    , delayStorage = case delayDefs of
                        Just d -> S.fromList d <> subsysStorage
                        Nothing -> error "delay mismatch"
                    , body = CIR.SScope $ case schedStmts of
                        Just s -> localDefs <> s
                        Nothing -> error "invalid schedule"
                    }
             in (context : newC, context : allC1)

  compose ([], _) = error "Missing main context"
  compose (mainC, allC) = CIR.Prog $ skepu <> [stdio] <> forwardDecls <> defs <> map main mainC
   where
    (forwardDecls, defs) = unzip . map contextToGlobal $ allC
    skepu = [ CIR.GMacro (ExId $ Name "ifdef") [ExId $ Name "__cplusplus"]
            , CIR.GMacro (ExId $ Name "include") [ExId $ Name "<skepu>"]
            , CIR.GMacro (ExId $ Name "include") [ExId $ Name "<skepu-lib/io.hpp>"]
            , CIR.GMacro (ExId $ Name "endif") []
            ]
    stdio = CIR.GMacro (ExId $ Name "include") [ExId $ Name "<stdio.h>"]
    getInput ret (t, v) = case removePoint t of
      CIR.TConstructor i t' ->
        [ CIR.SExpr $
            CIR.ECallExpr (CIR.EMemberAccess (CIR.EVar v) (ExId $ Name "init")) [CIR.EInt 10]
        ]
      _ ->
        [ CIR.SVarAssign
            ret
            (CIR.ECall (ExId $ Name "scanf") [CIR.EString $ typeToFormat t, CIR.EReference $ CIR.EVar v])
        ]
    putOutput (t, v) = case removePoint t of
      CIR.TConstructor _ t' ->
        [ CIR.SStream (ExId $ Name "skepu::io::cout") True $
          [ CIR.EVar v
          , CIR.EString "\\n"
          ]
        ]
      _ ->
        [ CIR.SExpr $
            CIR.ECall
              (ExId $ Name "printf")
              [ CIR.EString $ typeToFormat t <> "\\n"
              , CIR.EVar v
              ]
        ]
    typeToFormat ty = case removePoint ty of
      CIR.TInt -> "%d"
      CIR.TFloat -> "%f"
      CIR.TChar -> "%c"
      t -> error $ "unknown format string for " <> show t
    getArg (_, v) = CIR.EReference $ CIR.EVar v
    statusVar = ExId $ Name "status"
    main Context{..} =
      CIR.GFuncDef
        Nothing
        CIR.TInt
        (ExId $ Name "main")
        [(CIR.TInt, ExId $ Name "argc"), (CIR.TPointer . CIR.TPointer $ CIR.TChar, ExId $ Name "argv")]
        $ CIR.SScope
        $ map (\(t, v, e) -> CIR.SVarDef (removePoint t) v e) (S.elems delayStorage)
          <> [ CIR.SWhile (CIR.EInt 1) $
                 CIR.SScope $
                   map (\(t, v) -> CIR.SVarDecl (removePoint t) v) (inputs <> outputs)
                     <> [CIR.SVarDecl CIR.TInt statusVar]
                     <> (mconcat . map (getInput statusVar)) inputs
                     <> [ CIR.SIf
                            (CIR.EBinOp CIR.Less (CIR.EVar statusVar) (CIR.EInt 1))
                            (CIR.SScope [CIR.SBreak])
                            Nothing
                        ]
                     <> [ CIR.SExpr $
                            CIR.ECall (const IEmpty <$> from) $
                              map getArg $
                                inputs <> outputs <> (map (\(t, v, _) -> (t, v)) $ S.elems delayStorage)
                        ]
                     <> (mconcat . map putOutput) outputs
             ]
          <> [CIR.SReturn $ Just $ CIR.EInt $ -1]
    contextToGlobal Context{..} =
      ( CIR.GFuncDeclare (Just CIR.Static) ret (const IEmpty <$> from) $
          inputs <> outputs <> (map (\(t, n, _) -> (t, n)) . S.elems) delayStorage
      , CIR.GFuncDef
          (Just CIR.Static)
          ret
          (const IEmpty <$> from)
          (inputs <> outputs <> (map (\(t, n, _) -> (t, n)) . S.elems) delayStorage)
          body
      )
