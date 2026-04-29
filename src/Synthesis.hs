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
import qualified Data.Map as M
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
  , delay :: Bool
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
  TyConApp v1 [v2]
    | getOccString v1 == "Num" -> case v2 of
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
  TyConApp v1 _ | getOccString v1 == "Fractional" -> CIR.TFloat
  TyConApp v1 _ | getOccString v1 == "Integral" -> CIR.TInt
  TyConApp v a -> error $ "TyConApp: " <> (getOccString . tyConName) v <> " " <> showPprUnsafe a
  t -> error $ "Something else: " <> showPprUnsafe t

varToCType :: Var -> CType
varToCType = portToC . makePort . varType

exprToCType :: CoreExpr -> CType
exprToCType = \case
  Type t -> portToC . makePort $ t
  Var v -> varToCType v
  _ -> error "Not a type!"

varToCDef :: Var -> (CType, Id IdExt)
varToCDef v =
  let ty = varToCType v
      name = Direct v
   in (ty, name)

getDelayExpr :: CoreExpr -> Maybe CoreExpr
getDelayExpr = \case
  App (App (Var v) _) e | isDelayVar v -> Just e
  _ -> Nothing

delayExprToC :: CoreExpr -> CExpression
delayExprToC = \case
  App (Var _) (Lit (LitNumber _ i)) -> CIR.EInt . fromIntegral $ i
  App _ (Lit (LitFloat f)) -> CIR.EFloat $ fromRational f
  App _ (Lit (LitDouble f)) -> CIR.EFloat $ fromRational f
  _ -> undefined

inputIds :: [Id IdExt]
inputIds = map ((ExId Input <>) . Ix) [0 ..]
inputArgs :: [CExpression]
inputArgs = map CIR.EVar inputIds
outputIds :: [Id IdExt]
outputIds = map ((ExId Output <>) . Ix) [0 ..]
outputArgs :: [CExpression]
outputArgs = map CIR.EVar outputIds

vertexToExpr :: (Foldable t) => t (Id IdExt) -> [Context a] -> Vertex -> CExpression
vertexToExpr pointers context Vertex{id = _, ..} = case process of
  Right _ -> undefined
  Left v -> CIR.ECall (const IEmpty <$> v) $ map ioToExpr (map Direct inputs) <> map ioToExpr (map Direct outputs) <> (delayParams v)
 where
  delayParams v =
    S.elems
      . S.map (\(_, s, _) -> case s of
        ExId Tmp -> CIR.EVar . (<> ExId Tmp) . Direct . head $ outputs
        _ -> CIR.EVar s)
      . mconcat
      . map (\Context{delayStorage} -> delayStorage)
      . filter (\Context{from} -> v == from)
      $ context
  ioToExpr io =
    if elem io pointers
      then CIR.EVar io
      else CIR.EReference . CIR.EVar $ io

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
  "farm13" -> Just (FunArg, ExId Map <> (ExId $ Name "<1>"))
  "farm14" -> Just (FunArg, ExId Map <> (ExId $ Name "<1>"))
  "farm21" -> Just (FunArg, ExId Map <> (ExId $ Name "<2>"))
  "farm22" -> Just (FunArg, ExId Map <> (ExId $ Name "<2>"))
  "farm23" -> Just (FunArg, ExId Map <> (ExId $ Name "<2>"))
  "farm24" -> Just (FunArg, ExId Map <> (ExId $ Name "<2>"))
  "farm31" -> Just (FunArg, ExId Map <> (ExId $ Name "<3>"))
  "farm32" -> Just (FunArg, ExId Map <> (ExId $ Name "<3>"))
  "farm33" -> Just (FunArg, ExId Map <> (ExId $ Name "<3>"))
  "farm34" -> Just (FunArg, ExId Map <> (ExId $ Name "<3>"))
  "farm41" -> Just (FunArg, ExId Map <> (ExId $ Name "<4>"))
  "farm42" -> Just (FunArg, ExId Map <> (ExId $ Name "<4>"))
  "farm43" -> Just (FunArg, ExId Map <> (ExId $ Name "<4>"))
  "farm44" -> Just (FunArg, ExId Map <> (ExId $ Name "<4>"))
  _ -> Nothing

resolveOp ::
  Int ->
  [CStatement] ->
  [(CType, CExpression)] ->
  CType ->
  String ->
  (Int, [CStatement], (CType, CExpression))
resolveOp tmpix stmts [(t1, expr1)] tout = \case
  "length" -> case t1 of
    CIR.TConstructor _ _ -> (tmpix, stmts, (tout, CIR.ECallExpr (CIR.EMemberAccess expr1 (ExId $ Name "size")) []))
    _ -> error $ show t1
  u -> error $ "Unknown unary function: " <> u
resolveOp tmpix stmts [(t1, expr1), (t2, expr2)] tout = \case
  "+" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Add e1 e2))
  "*" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Multiply e1 e2))
  "-" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Subtract e1 e2))
  "quot" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "/" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "div" -> error "Haskell `div` rounds to negative infinity, not implemented. Consider using `quot`"
  u -> error $ "Unknown binary function: " <> u
 where
  e1 = derefArg (needDeref 0 (t1, tout)) expr1
  e2 = derefArg (needDeref 0 (t2, tout)) expr2
resolveOp _ _ _ _ = undefined

exprToLambda :: Int -> OutputLoc -> M.Map (Id IdExt) (CType, CExpression) -> [CType] -> CType -> [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
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
                (tmpix', stmts, (_, expr')) = resolveOp tmpix [] [(t1', CIR.EVar in1), (t2', CIR.EVar in2)] tout (getOccString f)
                expr'' = CIR.ELambda [] [(t1', in1), (t2', in2)] $ CIR.SScope [CIR.SReturn . Just $ expr']
             in (tmpix', stmts, (tout, expr''))
          _ -> undefined
  App (App (App (Var f) t1) t2) v1@(Var v)
    | typeOrConstraint t1 && typeOrConstraint t2 && (not $ typeOrConstraint v1) ->
        case (makePorts . extractTypes [] . varType $ f, M.lookup (Direct v) args) of
          -- A partially applied binary function, construct a lambda. Note that
          -- SkePU does not use variable capture, but instead passes it as a
          -- scalar.
          ((a1 : a2 : [], out : []), Just (argty1, arg1)) ->
            let in1 = ExId Input <> Ix 0
                t1' = exprToCType t1
                in2 = ExId Input <> Ix 1
                t2' = exprToCType t2
                (tmpix', stmts, (_, expr')) = resolveOp tmpix [] [(t1', CIR.EVar in1), (t2', CIR.EVar in2)] tout (getOccString f)
                expr'' = CIR.ELambda [] [(t1', in1), (t2', in2)] $ CIR.SScope [CIR.SReturn . Just $ expr']
             in (tmpix', stmts, (tout, expr''))
          _ -> undefined
  e@(Lam _ _) ->
    let (b1, e1) = collectBinders e
        args' = M.fromList . zipWith varToArgMap b1 $ inputIds
        varToArgMap v i = (Direct v, (varToCType v, CIR.EVar i))
    in exprToLambda tmpix outLoc (args' <> args) tin tout inports outports e1
  e ->
    let (tmpix1, stmts1, (_, expr1)) = exprToCExpr tmpix outLoc (M.map (\(t', e') -> (removePoint t', e')) args) tin tout inputs outports e
        inputs = zip tin inputIds
        expr2 = CIR.ELambda [] inputs $ CIR.SScope [CIR.SReturn $ Just expr1]
     in (tmpix1, stmts1, (tout, expr2))

-- Horrible, should trim arguments
skelAppToCExpr :: Int -> OutputLoc -> p1 -> [CStatement] -> [CType] -> CType -> [(CType, b2)] -> p2 -> Id IdExt -> CExpression -> (Int, [CStatement], (CType, CExpression))
skelAppToCExpr tmpix1 ret args stmts1 tin tout inports outports skel e1' =
  let (tmpix2, outname) = mkTemp tmpix1
      (tmpix3, skelInstance) = mkTemp tmpix2
      inputs = zipWith (derefTo CIR.TVoid) (map fst inports) inputArgs
      ini = case tout of
        CIR.TConstructor _ _ ->
          Just
            [ CIR.ECallExpr
                ( CIR.EMemberAccess
                    (derefTo CIR.TVoid (fst . head $ inports) $ head inputArgs)
                    (ExId $ Name "size")
                )
                []
            ]
        _ -> Nothing
      call =
        CIR.ECall skelInstance $
          case ret of
            FunArg -> [CIR.EVar outname] <> inputs
            Return -> [CIR.EDereference $ CIR.EVar $ ExId Input <> Ix 0]
      stmts =
        [ CIR.SVarDecl tout outname ini
        , CIR.SVarDef CIR.TAuto skelInstance Nothing $ CIR.ECall skel [e1']
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

exprToCExpr :: Int -> OutputLoc -> M.Map (Id IdExt) (CType, CExpression) -> [CType] -> CType -> [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToCExpr tmpix outLoc args tin tout inports outports expr = case expr of
  -- Inner function applied to a function and a var
  App (App (App (App (Var inner) t1) t2) e1) e2@(Var v)
    | typeOrConstraint t1 && typeOrConstraint t2 && (not $ typeOrConstraint e1) && (not $ typeOrConstraint e2) ->
        case skelToSkePU $ getOccString inner of
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args [exprToCType t1, exprToCType t2] tout inports outports e1
             in skelAppToCExpr tmpix1 ret args stmts1 tin tout inports outports skel e1'
          Nothing ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix FunArg args tin (exprToCType t1) inports outports e1
                (tmpix2, stmts2, (t2', expr2)) = exprToCExpr tmpix1 FunArg args tin (exprToCType t2) inports outports e2
             in resolveOp tmpix2 (stmts1 <> stmts2) [(t1', expr1), (t2', expr2)] tout $ getOccString inner
  -- Binary operator/function (with type variables)
  App (App (App (App (Var f) t1) t2) e1) e2
    | typeOrConstraint t1 && typeOrConstraint t2 && (not $ typeOrConstraint e1) && (not $ typeOrConstraint e2) ->
        let (tmpix1, stmts1, (_, expr1)) = exprToCExpr tmpix FunArg args tin (exprToCType t1) inports outports e1
            (tmpix2, stmts2, (_, expr2)) = exprToCExpr tmpix1 FunArg args tin (exprToCType t2) inports outports e2
         in resolveOp tmpix2 (stmts1 <> stmts2) [(exprToCType t1, expr1), (exprToCType t2, expr2)] tout $ getOccString f
  -- Inner function applied to a var
  App (App (App (App (Var f) t1) t2) t3) e1@(Var v1)
    | typeOrConstraint t1 && typeOrConstraint t2 && typeOrConstraint t3 && (not $ typeOrConstraint e1) ->
        case skelToSkePU (getOccString f) of
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args [exprToCType t1, exprToCType t2] (exprToCType t3) inports outports e1
             in skelAppToCExpr tmpix1 ret args stmts1 tin tout inports outports skel e1'
          -- A little weird
          Nothing ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix FunArg args tin (varToCType v1) inports outports e1
             in resolveOp tmpix1 stmts1 [(t1', expr1)] tout $ getOccString f
  -- Inner function applied to an expression
  App (App (App (App (Var f) t1) t2) t3) e1
    | typeOrConstraint t1 && typeOrConstraint t2 && typeOrConstraint t3 && (not $ typeOrConstraint e1) ->
        case skelToSkePU (getOccString f) of
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args [exprToCType t1, exprToCType t2] (exprToCType t3) inports outports e1
             in skelAppToCExpr tmpix1 ret args stmts1 tin tout inports outports skel e1'
          Nothing -> error . showPprUnsafe $ e1
  -- A partially applied binary operator passed as a value. Apply it to the input argument
  App (App (App (Var f) t1) t2) e
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        let (tmpix1, stmts1, (t1', e1)) = exprToCExpr tmpix FunArg args tin tout inports outports e
            v1 = derefTo (exprToCType t1) (fst . head $ inports) $ CIR.EVar $ ExId Input <> Ix 0
         in resolveOp tmpix1 stmts1 [(t1', e1), (head tin, v1)] tout $ getOccString f
  -- Inner unary function applied onto an expression and var
  App (App (App (Var inner) t1) e) (Var v)
    | typeOrConstraint t1 && (not $ typeOrConstraint e) ->
        case skelToSkePU (getOccString inner) of
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args [varToCType v] (exprToCType t1) inports outports e
             in skelAppToCExpr tmpix1 ret args stmts1 tin tout inports outports skel e1'
          Nothing -> undefined
  -- Unary operator/function (with type variables)
  App (App (Var f) t) (Var v) | typeOrConstraint t && (not $ typeOrConstraint $ Var v) ->
    case M.lookup (Direct v) args of
      Just (argty, arg) ->
        (tmpix, [], (tout, CIR.ECall (Direct f) [arg]))
      Nothing -> error $ "Var not in args! " <> showPprUnsafe expr
  -- Inner function applied to a function. Apply it to the input arguments
  App (App (Var inner) t) e
    | typeOrConstraint t && (not $ typeOrConstraint e) ->
        case skelToSkePU $ getOccString inner of
          Nothing -> error $ "Unknown skeleton: " <> getOccString inner
          Just (ret, skel) ->
            let (tmpix1, stmts1, (_, e1')) = exprToLambda tmpix ret args tin tout inports outports e
             in skelAppToCExpr tmpix1 ret args stmts1 tin tout inports outports skel e1'
  -- A binary operator passed as a value. Apply it to the input arguments
  App (App (Var f) t1) t2
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        resolveOp tmpix [] (take 2 $ M.elems args) tout $ getOccString f
  -- An integer literal
  App _ (Lit (LitNumber _ i)) -> (tmpix, [], (CIR.TInt, CIR.EInt $ fromIntegral i))
  Lit (LitNumber _ i) -> (tmpix, [], (CIR.TInt, CIR.EInt $ fromIntegral i))
  App _ (Lit (LitFloat f)) -> (tmpix, [], (CIR.TInt, CIR.EFloat $ fromRational f))
  Lit (LitFloat f) -> (tmpix, [], (CIR.TFloat, CIR.EFloat $ fromRational f))
  App _ (Lit (LitDouble f)) -> (tmpix, [], (CIR.TInt, CIR.EFloat $ fromRational f))
  Lit (LitDouble f) -> (tmpix, [], (CIR.TFloat, CIR.EFloat $ fromRational f))
  Var v -> case M.lookup (Direct v) args of
    Just (t', v') -> (tmpix, [], (tout, derefTo tout t' v'))
    -- Assume the Var is a function
    -- TODO: need to rethink multiple output
    Nothing ->
      let (inputs, outputs) = extractTypes [] . varType $ v
          (inPorts, outPorts) = makePorts . extractTypes [] . varType $ v
          inArgs = zipWith3 derefTo tin (map fst inports) inputArgs
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

derefTo :: CIR.Type a1 -> CIR.Type a2 -> CIR.Expression a -> CIR.Expression a
derefTo outty inty = derefArg (needDeref 0 (inty, outty))

-- | Make an argument map, from args if existent otherwise from ports
makeMap :: (Ord a1, Eq a2, Eq a3) => [CoreBndr] -> [(a2, Id a3)] -> M.Map (Id a1) (a2, CIR.Expression a3)
makeMap args ports =
  case M.fromList $ zipWith (\b (t, n) -> (Direct b, (t, CIR.EVar n))) args ports of
    m
      | m == mempty ->
          M.fromList $ zipWith (\ix (t, n) -> (Ix ix, (t, CIR.EVar n))) [0 ..] ports
      | otherwise -> m

makeComb :: [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> [CoreExpr] -> Expr CoreBndr -> (OutputLoc, CIR.Statement IdExt)
makeComb inports outports tys e =
  let (args, expr) = collectBinders e
      argMap = makeMap args inports
   in case expr of
        App (App (App (App (App (App (App (App (Var v') te1) te2) te3) te4) e1) e2) e3) e4
          | getOccString v' == "(,,,)" ->
              let tout1 = exprToCType te1
                  tout2 = exprToCType te2
                  tout3 = exprToCType te3
                  tout4 = exprToCType te4
                  (cntr, init1, (_, ea1)) = exprToCExpr 0 FunArg argMap (map exprToCType tys) tout1 inports outports e1
                  (cntr1, init2, (_, ea2)) = exprToCExpr cntr FunArg argMap (map exprToCType tys) tout2 inports outports e2
                  (cntr2, init3, (_, ea3)) = exprToCExpr cntr1 FunArg argMap (map exprToCType tys) tout3 inports outports e3
                  (_, init4, (_, ea4)) = exprToCExpr cntr2 FunArg argMap (map exprToCType tys) tout4 inports outports e4
               in ( FunArg
                  , CIR.SScope $
                      init1
                        <> init2
                        <> init3
                        <> init4
                        <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 1) ea2
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 2) ea3
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 3) ea4
                           ]
                  )
        App (App (App (App (App (App (Var v') te1) te2) te3) e1) e2) e3
          | getOccString v' == "(,,)" ->
              let tout1 = exprToCType te1
                  tout2 = exprToCType te2
                  tout3 = exprToCType te3
                  (cntr, init1, (_, ea1)) = exprToCExpr 0 FunArg argMap (map exprToCType tys) tout1 inports outports e1
                  (cntr1, init2, (_, ea2)) = exprToCExpr cntr FunArg argMap (map exprToCType tys) tout2 inports outports e2
                  (_, init3, (_, ea3)) = exprToCExpr cntr1 FunArg argMap (map exprToCType tys) tout3 inports outports e3
               in ( FunArg
                  , CIR.SScope $
                      init1
                        <> init2
                        <> init3
                        <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 1) ea2
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 2) ea3
                           ]
                  )
        App (App (App (App (Var v') te1) te2) e1) e2
          | getOccString v' == "(,)" ->
              let tout1 = exprToCType te1
                  tout2 = exprToCType te2
                  (cntr, init1, (_, ea1)) = exprToCExpr 0 FunArg argMap (map exprToCType tys) tout1 inports outports e1
                  (_, init2, (_, ea2)) = exprToCExpr cntr FunArg argMap (map exprToCType tys) tout2 inports outports e2
               in ( FunArg
                  , CIR.SScope $
                      init1
                        <> init2
                        <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 1) ea2
                           ]
                  )
        _ ->
            let tout1 = exprToCType $ last tys
                (_, init1, (_, ea1)) = exprToCExpr 0 FunArg argMap (map exprToCType $ init tys) tout1 inports outports expr
             in ( FunArg
                , CIR.SScope $
                    init1
                      <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1 ]
                )

bodyToStatement :: [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (OutputLoc, CStatement)
bodyToStatement inports outports = \case
  App (App (App (App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12) e
    | getOccString v == "comb84" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12] e
    | otherwise -> error $ "13App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) e
    | getOccString v == "comb74" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] e
    | getOccString v == "comb83" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] e
    | otherwise -> error $ "12App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) e
    | getOccString v == "comb64" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] e
    | getOccString v == "comb73" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] e
    | getOccString v == "comb82" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] e
    | otherwise -> error $ "11App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) e
    | getOccString v == "comb54" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | getOccString v == "comb63" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | getOccString v == "comb72" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | getOccString v == "comb81" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | otherwise -> error $ "10App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) e
    | getOccString v == "comb44" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | getOccString v == "comb53" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | getOccString v == "comb62" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | getOccString v == "comb71" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | otherwise -> error $ "9App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) e
    | getOccString v == "comb34" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | getOccString v == "comb43" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | getOccString v == "comb52" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | getOccString v == "comb61" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | otherwise -> error $ "8App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) e
    | getOccString v == "comb24" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | getOccString v == "comb33" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | getOccString v == "comb42" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | getOccString v == "comb51" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | otherwise -> error $ "7App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) e
    | getOccString v == "comb14" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | getOccString v == "comb23" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | getOccString v == "comb32" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | getOccString v == "comb41" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | otherwise -> error $ "6App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (App (Var v) t1) t2) t3) t4) e
    | getOccString v == "comb13" -> makeComb inports outports [t1, t2, t3, t4] e
    | getOccString v == "comb22" -> makeComb inports outports [t1, t2, t3, t4] e
    | getOccString v == "comb31" -> makeComb inports outports [t1, t2, t3, t4] e
    | otherwise -> error $ "5App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (App (Var v) t1) t2) t3) e
    | getOccString v == "comb12" -> makeComb inports outports [t1, t2, t3] e
    | getOccString v == "comb21" -> makeComb inports outports [t1, t2, t3] e
    | otherwise -> error $ "4App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (App (Var v) t1) t2) e
    | getOccString v == "comb11" -> makeComb inports outports [t1, t2]  e
    | otherwise -> error $ "3App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (App (Var v) _) e
    | getOccString v == "delay" ->
        (FunArg, delayBody)
    | otherwise -> error $ "2App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  App (Var v) e -> error $ "1App(" <> show (Direct v :: Id ()) <> "): " <> showPprUnsafe e
  -- Might be a regular function, i.e. not a process
  e@(Lam _ _) ->
    let (args, expr') = collectBinders e
        argMap = makeMap args inports
        (_, stmts, (_, expr)) = exprToCExpr 0 Return argMap (map fst inports) (fst . head $ outports) inports outports expr'
     in ( Return
        , CIR.SScope $
            stmts
              <> [CIR.SReturn . Just $ expr]
        )
  e -> error . showPprUnsafe $ e
  where
    -- The delay can both be used on intermediary signals and input/output
    -- signals. When used on an output signal, it needs to also output the
    -- current value of the delay, hence the shuffling of values.
    delayBody =
      CIR.SScope
        [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) (CIR.EDereference . CIR.EVar $ ExId Tmp)
        , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Tmp) (CIR.EDereference . CIR.EVar $ ExId Input <> Ix 0)
        ]

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
                delayExpr = case body of
                  App (App (Var v) _) e
                    | isDelayVar v -> Just $ delayExprToC e
                  _ -> Nothing
                context =
                  Context
                    { from = binder
                    , ret = case retLoc of
                        FunArg -> CIR.TVoid
                        Return -> fst . head $ outputs
                    , inputs
                    , outputs = case retLoc of
                        FunArg -> outputs
                        Return -> mempty
                    , delayStorage = case delayExpr of
                      Just e -> S.singleton (fst . head $ outputs, ExId Tmp, e)
                      _ -> mempty
                    , delay = case delayExpr of
                      Just _ -> True
                      Nothing -> False
                    , body = body'
                    }
             in (context : newC, context : allC)
          Just System{..} ->
            let procs' = filter (/= p) procs
                systemProcs = S.elems . mconcat . map (vertexProcs (S.fromList procs)) $ vertices
                (subsysNew, allC1) = foldr (synthesize procs') (newC, allC) systemProcs
                inDefs = map varToCDef inputs
                outDefs = map varToCDef outputs
                delays = mapMaybe delayVertex vertices
                delayProcs = mconcat . map (delayProc procs) $ delays
                delayBodies = sequence . map (getDelayExpr . \Process{body = b} -> b) $ delayProcs
                delayExprs = map delayExprToC <$> delayBodies
                delaySigs =
                  mconcat
                    . map
                      ( \v@Vertex{outputs = outputs'} ->
                          if length outputs' == 1
                            then outputs'
                            else error $ "invalid delay outputs: " <> show v
                      )
                    $ delays
                delayTypes = map varToCDef delaySigs
                delayDefs = delayExprs >>= \_c -> Just $ ((\(t, v) e -> (t, v <> ExId Tmp, e)) <$> delayTypes) <*> _c
                subsysStorage = mconcat . mapMaybe (\Context{delayStorage, delay} -> if delay then Nothing else Just delayStorage) $ subsysNew
                findVert vid = find (\Vertex{id = i} -> i == vid) vertices
                schedVert = mapMaybe findVert <$> schedule
                delaySigs' = map (\b -> Direct b <> ExId Tmp) delaySigs
                pointers = delaySigs' <> map Direct inputs <> map Direct outputs
                schedStmts = map (CIR.SExpr . vertexToExpr pointers subsysNew) <$> schedVert
                locals = S.filter (\v -> not (elem (Direct v) (pointers <> map Direct delaySigs))) . S.fromList . map (\(Edge v _ _) -> v) $ edges
                localDefs = S.map ((\(t, s) -> CIR.SVarDecl t s Nothing) . (\(t, n) -> (removePoint t, n)) . varToCDef) locals
                delayTmps = map (\(t, i) -> CIR.SVarDef (removePoint t) i Nothing (CIR.EDereference . CIR.EVar $ i <> ExId Tmp)) delayTypes
                context =
                  Context
                    { from = binder
                    , ret = CIR.TVoid
                    , inputs = inDefs
                    , outputs = outDefs
                    , delay = False
                    , delayStorage = case delayDefs of
                        Just d -> S.fromList d <> subsysStorage
                        Nothing -> error "delay mismatch"
                    , body = CIR.SScope $ case schedStmts of
                        Just s -> S.elems localDefs <> delayTmps <> s
                        Nothing -> error "invalid schedule"
                    }
             in (context : newC, context : allC1)

  compose ([], _) = error "Missing main context"
  compose (mainC, allC) = CIR.Prog $ skepu <> [stdio] <> forwardDecls <> defs <> map main mainC
   where
    (forwardDecls, defs) = unzip . map contextToGlobal $ allC
    skepu =
      [ CIR.GMacro (ExId $ Name "ifdef") [ExId $ Name "__cplusplus"]
      , CIR.GMacro (ExId $ Name "include") [ExId $ Name "<skepu>"]
      , CIR.GMacro (ExId $ Name "include") [ExId $ Name "<skepu-lib/io.hpp>"]
      , CIR.GMacro (ExId $ Name "endif") []
      ]
    stdio = CIR.GMacro (ExId $ Name "include") [ExId $ Name "<stdio.h>"]
    getInput ret (t, v) = case removePoint t of
      CIR.TConstructor i t' ->
        [ CIR.SExpr $
            CIR.ECall (ExId $ Name "skepu::external") $
              [ CIR.ELambda [ExId $ Name "&"] [] $
                  CIR.SScope $
                    [ CIR.SVarDecl CIR.TSizeT (ExId Tmp <> Ix 0) Nothing
                    , CIR.SVarDecl t' (ExId Input) Nothing
                    ]
                      <> getInput statusVar (CIR.TSizeT, ExId Tmp <> Ix 0)
                      <> breakInput (CIR.SReturn Nothing)
                      <> [ CIR.SExpr $
                             CIR.ECallExpr (CIR.EMemberAccess (CIR.EVar v) (ExId $ Name "init")) [CIR.EVar $ ExId Tmp <> Ix 0]
                         ]
                      <> [ CIR.SFor
                             (CIR.SVarDef CIR.TSizeT (ExId Tmp <> Ix 1) Nothing (CIR.EInt 0))
                             (CIR.EBinOp CIR.Less (CIR.EVar $ ExId Tmp <> Ix 1) (CIR.EVar $ ExId Tmp <> Ix 0))
                             (CIR.SExpr $ CIR.EUnOp CIR.PostIncrement (CIR.EVar $ ExId Tmp <> Ix 1))
                             $ CIR.SScope
                             $ (getInput statusVar (t', ExId Input))
                               <> [ CIR.SAssign
                                      (CIR.ECall v [CIR.EVar (ExId Tmp <> Ix 1)])
                                      (CIR.EVar $ ExId Input)
                                  ]
                         ]
              , CIR.ECall (ExId $ Name "skepu::write") [CIR.EVar v]
              ]
        ]
          <> breakInput CIR.SBreak
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
      CIR.TSizeT -> "%zu"
      t -> error $ "unknown format string for " <> show t
    getArg (_, v) = CIR.EReference $ CIR.EVar v
    statusVar = ExId $ Name "status"
    breakInput stmt =
      [ CIR.SIf
          (CIR.EBinOp CIR.Less (CIR.EVar statusVar) (CIR.EInt 1))
          (CIR.SScope [stmt])
          Nothing
      ]
    main Context{..} =
      CIR.GFuncDef
        Nothing
        CIR.TInt
        (ExId $ Name "main")
        [(CIR.TInt, ExId $ Name "argc"), (CIR.TPointer . CIR.TPointer $ CIR.TChar, ExId $ Name "argv")]
        $ CIR.SScope
        $ map (\(t, v, e) -> CIR.SVarDef (removePoint t) v Nothing e) (S.elems delayStorage)
          <> [ CIR.SWhile (CIR.EInt 1) $
                 CIR.SScope $
                   map (\(t, v) -> CIR.SVarDecl (removePoint t) v Nothing) (inputs <> outputs)
                     <> [CIR.SVarDef CIR.TInt statusVar Nothing (CIR.EInt 1)]
                     <> (mconcat . map (getInput statusVar)) inputs
                     <> breakInput CIR.SBreak
                     <> [ CIR.SExpr $
                            CIR.ECall (const IEmpty <$> from) $
                              map getArg $
                                inputs <> outputs <> (S.elems $ S.map (\(t, v, _) -> (t, v)) $ delayStorage)
                        ]
                     <> (mconcat . map putOutput) outputs
             ]
          <> [CIR.SReturn $ Just $ CIR.EInt $ -1]
    contextToGlobal Context{..} =
      ( CIR.GFuncDeclare (Just CIR.Static) ret (const IEmpty <$> from) $
          inputs <> outputs <> (S.elems . S.map (\(t, n, _) -> (t, n))) delayStorage
      , CIR.GFuncDef
          (Just CIR.Static)
          ret
          (const IEmpty <$> from)
          (inputs <> outputs <> (S.elems . S.map (\(t, n, _) -> (t, n))) delayStorage)
          body
      )
