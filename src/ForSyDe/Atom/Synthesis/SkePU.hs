{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module ForSyDe.Atom.Synthesis.SkePU (
  CContext (..),
  Synthesizable (..),
) where

import GHC.Core
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Types.Literal
import GHC.Types.Name (getOccString)
import GHC.Utils.Outputable (showPprUnsafe)

import qualified ForSyDe.Atom.Synthesis.CIR as CIR
import Data.List (find, sort)
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import ForSyDe.Atom.Synthesis.IR as IR
import Prettyprinter

data IdExt
  = Name String
  | Input
  | Output
  | Delay
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
  pretty Delay = pretty "delay"
  pretty Tmp = pretty "tmp"
  pretty IVector = pretty "skepu::Vector"
  pretty IMatrix = pretty "skepu::Matrix"
  pretty IEmpty = mempty
  pretty Reduce = pretty "skepu::Reduce"
  pretty Map = pretty "skepu::Map"

type CType = CIR.Type (Id IdExt)
type CExpression = CIR.Expression (Id IdExt)
type CStatement = CIR.Statement (Id IdExt)
type CProgram = CIR.Program (Id IdExt)

data CContext = CContext
  { from :: Id ()
  , ret :: CType
  , inputs :: [(CType, Id IdExt)]
  , outputs :: [(CType, Id IdExt)]
  , delayStorage :: S.Set (CType, Id IdExt, CExpression)
  , delay :: Bool
  , body :: CStatement
  , program :: Maybe CProgram
  }
  deriving (Show)
instance Pretty CContext where
  pretty CContext{..} =
    pretty "Context"
      <> (nest 4 . tupled)
        [ pretty from
        , pretty ret
        , pretty inputs
        , pretty outputs
        , pretty . S.elems $ delayStorage
        , pretty body
        ]

-- | Map Ports into C types
portToC :: Port -> CType
portToC = \case
  Signal a _ _ -> CIR.TPointer $ portToC a
  AbstExt a _ -> portToC a
  Vector (Vector p _) _ ->
    CIR.TConstructor (CIR.TIdent $ ExId IMatrix) (portToC p)
  Vector p _ ->
    CIR.TConstructor (CIR.TIdent $ ExId IVector) (portToC p)
  Opaque t -> typeToCType t

-- | Map GHC types into C types
typeToCType :: Type -> CType
typeToCType = \case
  TyVarTy v
    | getOccString v == "Int" -> CIR.TLong
    | getOccString v == "Integer" -> CIR.TLong
    | getOccString v == "Float" -> CIR.TFloat
    | getOccString v == "Double" -> CIR.TDouble
  TyVarTy v -> error $ "TyVarTy: " <> showPprUnsafe v
  TyConApp v []
    | getOccString v == "Int" -> CIR.TLong
    | getOccString v == "Integer" -> CIR.TLong
    | getOccString v == "Float" -> CIR.TFloat
    | getOccString v == "Double" -> CIR.TDouble
  TyConApp v1 [v2]
    | getOccString v1 == "Num" -> case v2 of
      TyVarTy v2'
        | getOccString v2' == "Integer" -> CIR.TLong
        | getOccString v2' == "Int" -> CIR.TLong
        | getOccString v2' == "Float" -> CIR.TFloat
        | getOccString v2' == "Double" -> CIR.TDouble
      TyConApp v2' _
        | getOccString v2' == "Integer" -> CIR.TLong
        | getOccString v2' == "Int" -> CIR.TLong
        | getOccString v2' == "Float" -> CIR.TFloat
        | getOccString v2' == "Double" -> CIR.TDouble
      _ -> error . showPprUnsafe $ v2
    | getOccString v1 == "Ord" -> case v2 of
      TyVarTy v2'
        | getOccString v2' == "Integer" -> CIR.TLong
        | getOccString v2' == "Int" -> CIR.TLong
        | getOccString v2' == "Float" -> CIR.TFloat
        | getOccString v2' == "Double" -> CIR.TDouble
      TyConApp v2' _
        | getOccString v2' == "Integer" -> CIR.TLong
        | getOccString v2' == "Int" -> CIR.TLong
        | getOccString v2' == "Float" -> CIR.TFloat
        | getOccString v2' == "Double" -> CIR.TDouble
      _ -> error . showPprUnsafe $ v2
  TyConApp v1 _ | getOccString v1 == "Floating" -> CIR.TFloat
  TyConApp v1 _ | getOccString v1 == "Fractional" -> CIR.TFloat
  TyConApp v1 _ | getOccString v1 == "Integral" -> CIR.TLong
  TyConApp v a -> error $ "TyConApp: " <> (getOccString . tyConName) v <> " " <> showPprUnsafe a
  t -> error $ "Something else: " <> showPprUnsafe t

-- | Make a C type of a GHC var
varToCType :: Var -> CType
varToCType = portToC . makePort . varType

-- | Make a C type of a GHC Core expression.
-- NOTE: should only be used on GHC types or vars
exprToCType :: CoreExpr -> CType
exprToCType = \case
  Type t -> portToC . makePort $ t
  Var v -> varToCType v
  _ -> error "Not a type!"

-- | Make a C type and Id pair from a GHC Core binder
varToCDef :: Var -> (CType, Id IdExt)
varToCDef v =
  let ty = varToCType v
      name = Direct v
   in (ty, name)

-- | Extract the initial value of a delay
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

-- | Make a new temporary identifier
mkTemp :: Int -> (Int, Id IdExt)
mkTemp ix = (ix + 1, ExId Tmp <> Ix ix)

data OutputLoc
  = FunArg
  | Return

-- Get the corresponding SkePU skeleton from the function name
skelToSkePU :: String -> Maybe (OutputLoc, Id IdExt)
skelToSkePU = \case
  "reducei" -> Just (Return, ExId Reduce)
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

-- | Match names of functions to C operations.
resolveOp ::
  Int ->
  [CStatement] ->
  [(CType, CExpression)] ->
  CType ->
  String ->
  (Int, [CStatement], (CType, CExpression))
resolveOp tmpix stmts [(t1, expr1)] tout = \case
  "length" -> case t1 of
    CIR.TConstructor _ _ -> (tmpix, stmts, (tout, CIR.ECallExpr (CIR.EMemberAccess e1 (ExId $ Name "size")) []))
    _ -> error $ show t1
  "id" -> (tmpix, stmts, (tout, e1))
  u -> error $ "Unknown unary function: " <> u
 where
  e1 = derefTo tout t1 expr1
resolveOp tmpix stmts [(t1, expr1), (t2, expr2)] tout = \case
  "+" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Add e1 e2))
  "*" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Multiply e1 e2))
  "-" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Subtract e1 e2))
  "quot" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "/" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "div" -> error "Haskell `div` rounds to negative infinity, not implemented. Consider using `quot`"
  "const" -> (tmpix, stmts, (tout, e1))
  "max" -> (tmpix, stmts, (tout, CIR.ETernary (CIR.EBinOp CIR.Greater e1 e2) e1 e2))
  "min" -> (tmpix, stmts, (tout, CIR.ETernary (CIR.EBinOp CIR.Less e1 e2) e1 e2))
  u -> error $ "Unknown binary function: " <> u
 where
  e1 = derefTo tout t1 expr1
  e2 = derefTo tout t2 expr2
resolveOp _ _ _ _ = undefined

-- | Wrap a C expression into a lambda, returning that as a statement and the
-- expression to call it.
exprToLambda :: Int -> OutputLoc -> [((Id IdExt), (CType, CExpression))] -> [Id IdExt] -> [CType] -> CType -> [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToLambda tmpix outLoc args largs tin tout inports outports expr = case expr of
  -- A function passed as a value (with type constraints). Construct a lambda
  App (App (Var f) t1) t2
    | typeOrConstraint t1 && typeOrConstraint t2 ->
        case makePorts . extractTypes [] . varType $ f of
          (_ : _ : [], _ : []) ->
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
        case (makePorts . extractTypes [] . varType $ f, lookup (Direct v) args) of
          -- A partially applied binary function, construct a lambda. Note that
          -- SkePU does not use variable capture, but instead passes it as a
          -- scalar.
          ((_ : _ : [], _ : []), Just (_, _)) ->
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
        args' = map varToArgMap b1
        varToArgMap v = (Direct v, (varToCType v, CIR.EVar (Direct v)))
    in exprToLambda tmpix outLoc (args' <> args) largs tin tout inports outports e1
  e ->
    let args' = map (\(i1, (t, i2)) -> (i1, (removePoint t, i2))) args
        (tmpix1, stmts1, (_, expr1)) = exprToCExpr tmpix args' tin tout (zip tin inputIds) outports e
        inExpr = CIR.getVars expr1
        explicit = map (\(i, _) -> i) . filter (\(i, _) -> elem i inExpr) $ args'
        notInArgs = filter (not . flip elem explicit) . sort $ inExpr
        -- Implicit arguments, i.e. eta-reduced ones
        implicit = take (length tin - length explicit) $ notInArgs
        -- Explicit arguments specified by Lams
        inputs = zip tin $ implicit <> explicit
        expr2 = CIR.ELambda [] inputs $ CIR.SScope [CIR.SReturn $ Just expr1]
     in (tmpix1, stmts1, (tout, expr2))

-- | Apply a skeleton instance to its arguments
skelAppToCExpr :: Int -> OutputLoc -> [((Id IdExt), (CType, CExpression))] -> [CStatement] -> [CType] -> CType -> [(CType, b2)] -> Id IdExt -> CExpression -> (Int, [CStatement], (CType, CExpression))
skelAppToCExpr tmpix1 ret args stmts1 tin tout inports skel e1' =
  let (tmpix2, outname) = mkTemp tmpix1
      (tmpix3, skelInstance) = mkTemp tmpix2
      inputs = zipWith3 derefTo tin (map fst inports) (map (snd . snd) args)
      ini = case (tout, inports, args) of
        (CIR.TConstructor _ _, (inty, _) : _, (_, (_, expr)) : _) ->
          Just
            [ CIR.ECallExpr
                ( CIR.EMemberAccess
                    (derefTo CIR.TVoid inty expr)
                    (ExId $ Name "size")
                )
                []
            ]
        _ -> Nothing
      call =
        CIR.ECall skelInstance $
          case ret of
            FunArg -> [CIR.EVar outname] <> inputs
            Return -> inputs
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

-- | Decompose applications to a base expression, types, argument expressions,
-- and argument vars
decomposeExpr :: Expr CoreBndr -> (Expr CoreBndr, [Arg CoreBndr], [Expr CoreBndr], [CoreBndr])
decomposeExpr = goVars []
 where
  goVars argVars = \case
    App e1 e2@(Var v) | not . typeOrConstraint $ e2 -> goVars (v : argVars) e1
    expr -> goExprs [] argVars expr
  goExprs argExprs argVars = \case
    App e1 e2 | not . typeOrConstraint $ e2 -> goExprs (e2 : argExprs) argVars e1
    expr -> goTys [] argExprs argVars expr
  goTys tys argExprs argVars = \case
    App e1 t1 | typeOrConstraint t1 -> goTys (t1 : tys) argExprs argVars e1
    expr -> (expr, tys, argExprs, argVars)

-- | Decompose expression and check for skeleton and type
decomposeAndSkeleton :: Expr CoreBndr -> (Expr CoreBndr, Maybe ([Type], [Type]), Maybe (OutputLoc, Id IdExt), [Arg CoreBndr], [Expr CoreBndr], [Expr CoreBndr], [CoreBndr])
decomposeAndSkeleton e = case decomposeExpr e of
  (base@(Var v), tys, exprs, vars) ->
    (base, Just $ extractTypes [] . varType $ v, skelToSkePU . getOccString $ v, tys, exprs <> map Var vars, exprs, vars)
  (base, tys, exprs, vars) ->
    (base, Nothing, Nothing, tys, exprs <> map Var vars, exprs, vars)

-- | Traverse a GHC Core expression and transform it into a C expression (and
-- possibly statements).
exprToCExpr :: Int -> [((Id IdExt), (CType, CExpression))] -> [CType] -> CType -> [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToCExpr tmpix args tin tout inports outports expr = case expr of
  -- Literals
  App _ (Lit (LitNumber _ i)) -> (tmpix, [], (CIR.TLong, CIR.EInt $ fromIntegral i))
  Lit (LitNumber _ i) -> (tmpix, [], (CIR.TLong, CIR.EInt $ fromIntegral i))
  App _ (Lit (LitFloat f)) -> (tmpix, [], (CIR.TFloat, CIR.EFloat $ fromRational f))
  Lit (LitFloat f) -> (tmpix, [], (CIR.TFloat, CIR.EFloat $ fromRational f))
  App _ (Lit (LitDouble f)) -> (tmpix, [], (CIR.TDouble, CIR.EFloat $ fromRational f))
  Lit (LitDouble f) -> (tmpix, [], (CIR.TDouble, CIR.EFloat $ fromRational f))
  Var v -> case lookup (Direct v) args of
    Just (t', v') -> (tmpix, [], (tout, derefTo tout t' v'))
    -- Assume the Var is a function
    -- TODO: need to rethink multiple output
    Nothing ->
      let (_, outputs) = makePorts . extractTypes [] . varType $ v
          inArgs = zipWith3 derefTo tin (map fst inports) inputArgs
       in if length outputs == 1
            then (tmpix, [], (portToC . head $ outputs, CIR.ECall (Direct v) inArgs))
            else error "user functions with multiple output is currently unsupported"
  e ->
    case decomposeAndSkeleton e of
      -- Reduce(i)
      (Var v, _, Just (ret, skel), tys, _, [fun, ini], [input]) | getOccString v == "reducei" ->
        let (tmpix1, stmts1, (_, eIni)) = exprToCExpr tmpix args tin tout inports outports ini
            (tmpix2, stmts2, (_, e1)) = exprToLambda tmpix1 ret args [Direct input] (map exprToCType . take (length tin) $ tys) tout inports outports fun
            (tmpix3, stmts3, (t2, e2)) = skelAppToCExpr tmpix2 ret args (stmts1 <> stmts2) tin tout inports skel e1
         in case e2 of
          CIR.ECall skelInstance _ ->
            let stmts4 = [CIR.SExpr $ CIR.ECallExpr (CIR.EMemberAccess (CIR.EVar skelInstance) (ExId $ Name "setStartValue")) [eIni]]
            in (tmpix3, stmts1 <> stmts2 <> stmts3 <> stmts4, (t2, e2))
          _ -> undefined -- This should not happen, skelApptToCExpr will always pass a ECall
      -- All skeleton farm applications
      (_, _, Just (ret, skel), tys, _, [argExpr], argVars) ->
        let (tmpix1, stmts1, (_, e1)) = exprToLambda tmpix ret args (map Direct argVars) (map exprToCType . take (length tin) $ tys) tout inports outports argExpr
         in skelAppToCExpr tmpix1 ret args stmts1 tin tout inports skel e1
      -- Vector length (has a weird type application due to parametrised output Num a)
      (Var inner, Just ([_], [_]), _, [_, _, _], [e1], _, _) ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType e1) inports outports e1
             in resolveOp tmpix1 stmts1 [(t1', expr1)] tout $ getOccString inner
      -- A fully applied binary function (two parametrised types)
      (Var inner, Just ([_, _], [_]), _, [t1, t2], [e1, e2], _, _) ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports outports e1
                (tmpix2, stmts2, (t2', expr2)) = exprToCExpr tmpix1 args tin (exprToCType t2) inports outports e2
             in resolveOp tmpix2 (stmts1 <> stmts2) [(t1', expr1), (t2', expr2)] tout $ getOccString inner
      -- A partially applied binary function (two parametrised types)
      (Var inner, Just ([_, _], [_]), _, [t1, t2], [e1], _, _) ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports outports e1
                v1 = derefTo (exprToCType t1) (fst . head $ inports) $ CIR.EVar $ ExId Input <> Ix 0
             in resolveOp tmpix1 stmts1 [(t1', expr1), (exprToCType t2, v1)] tout $ getOccString inner
      -- An unapplied binary function (two parametrised types)
      (Var inner, Just ([_, _], [_]),  _, [_, _], [], [], []) ->
             resolveOp 0 [] (take 2 . map snd $ args) tout $ getOccString inner
      -- A fully applied unary function (one parametrised type)
      (Var inner, Just ([_], [_]), _, [t1], [e1], _, _) ->
            let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports outports e1
             in resolveOp tmpix1 stmts1 [(t1', expr1)] tout $ getOccString inner
      -- An unapplied unary function (one parametrised type)
      (Var inner, Just ([_], [_]),  _, [_], [], [], []) ->
             resolveOp 0 [] (take 1 . map snd $ args) tout $ getOccString inner
      (_, ty, _, _, _, _, _) -> error $ showPprUnsafe e <> " " <> showPprUnsafe ty

-- | Compute the difference in pointer type
needDeref :: (Num t) => t -> (CIR.Type a1, CIR.Type a2) -> t
needDeref cur = \case
  (CIR.TPointer argTy, CIR.TPointer parmTy) -> needDeref cur (argTy, parmTy)
  (CIR.TPointer argTy, parmTy) -> needDeref (cur + 1) (argTy, parmTy)
  (argTy, CIR.TPointer parmTy) -> needDeref (cur - 1) (argTy, parmTy)
  _ -> cur

-- | Dereference (or form a reference of) an expression `num` times.
derefArg :: (Ord t, Num t) => t -> CIR.Expression a -> CIR.Expression a
derefArg num var = case compare num 0 of
  LT -> derefArg (num + 1) $ CIR.EReference var
  GT -> derefArg (num - 1) $ CIR.EDereference var
  EQ -> var

-- | Dereference (or form a reference of) an expression of `inty` until it
-- matches `outty`
derefTo :: CIR.Type a1 -> CIR.Type a2 -> CIR.Expression a -> CIR.Expression a
derefTo outty inty = derefArg (needDeref (0 :: Int) (inty, outty))

-- | Make an argument map, from args if existent otherwise from ports
makeMap :: (Ord a, Eq a2) => [CoreBndr] -> [(a2, Id a)] -> [((Id a), (a2, CIR.Expression (Id a)))]
makeMap args ports =
  case zipWith (\b (t, _) -> (Direct b, (t, CIR.EVar (Direct b)))) args ports of
    m
      | m == mempty ->
          map (\(t, n) -> (n, (t, CIR.EVar n))) ports
      | otherwise -> m

-- | Create processes using combNM. Note that only the number of tupled outputs
-- will change how it is processed, meaning this could accept any combNM where
-- M in [1,4].
makeComb :: [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> [CoreExpr] -> Expr CoreBndr -> (OutputLoc, [((Id IdExt), (CType, CExpression))], CStatement)
makeComb inports outports tys e =
  -- TODO: should split the input args and outputs
  let (args, expr) = collectBinders e
      argMap = makeMap args inports
      outArgs = makeMap [] outports
   in case expr of
        App (App (App (App (App (App (App (App (Var v') te1) te2) te3) te4) e1) e2) e3) e4
          | getOccString v' == "(,,,)" ->
              let tout1 = exprToCType te1
                  tout2 = exprToCType te2
                  tout3 = exprToCType te3
                  tout4 = exprToCType te4
                  tys' = map exprToCType . take (length tys - 4) $ tys
                  (cntr, init1, (_, ea1)) = exprToCExpr 0 argMap tys' tout1 inports outports e1
                  (cntr1, init2, (_, ea2)) = exprToCExpr cntr argMap tys' tout2 inports outports e2
                  (cntr2, init3, (_, ea3)) = exprToCExpr cntr1 argMap tys' tout3 inports outports e3
                  (_, init4, (_, ea4)) = exprToCExpr cntr2 argMap tys' tout4 inports outports e4
               in ( FunArg
                  , argMap <> outArgs
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
                  tys' = map exprToCType . take (length tys - 3) $ tys
                  (cntr, init1, (_, ea1)) = exprToCExpr 0 argMap tys' tout1 inports outports e1
                  (cntr1, init2, (_, ea2)) = exprToCExpr cntr argMap tys' tout2 inports outports e2
                  (_, init3, (_, ea3)) = exprToCExpr cntr1 argMap tys' tout3 inports outports e3
               in ( FunArg
                  , argMap <> outArgs
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
                  tys' = map exprToCType . take (length tys - 2) $ tys
                  (cntr, init1, (_, ea1)) = exprToCExpr 0 argMap tys' tout1 inports outports e1
                  (_, init2, (_, ea2)) = exprToCExpr cntr argMap tys' tout2 inports outports e2
               in ( FunArg
                  , argMap <> outArgs
                  , CIR.SScope $
                      init1
                        <> init2
                        <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1
                           , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 1) ea2
                           ]
                  )
        _ ->
            let tout1 = exprToCType $ last tys
                (_, init1, (_, ea1)) = exprToCExpr 0 argMap (map exprToCType $ init tys) tout1 inports outports expr
             in ( FunArg
                , argMap <> outArgs
                , CIR.SScope $
                    init1
                      <> [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) ea1 ]
                )

-- | Here all the process constructors are recognised and either passed to a
-- helper or processed dierectly
bodyToStatement :: [(CType, Id IdExt)] -> [(CType, Id IdExt)] -> CoreExpr -> (OutputLoc, [((Id IdExt), (CType, CExpression))], CStatement)
bodyToStatement inports outports = \case
  App (App (App (App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) t12) e
    | getOccString v == "comb84" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12] e
  App (App (App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11) e
    | getOccString v == "comb74" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] e
    | getOccString v == "comb83" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] e
  App (App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) e
    | getOccString v == "comb64" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] e
    | getOccString v == "comb73" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] e
    | getOccString v == "comb82" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] e
  App (App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) t9) e
    | getOccString v == "comb54" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | getOccString v == "comb63" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | getOccString v == "comb72" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
    | getOccString v == "comb81" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8, t9] e
  App (App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) t8) e
    | getOccString v == "comb44" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | getOccString v == "comb53" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | getOccString v == "comb62" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
    | getOccString v == "comb71" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7, t8] e
  App (App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) t7) e
    | getOccString v == "comb34" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | getOccString v == "comb43" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | getOccString v == "comb52" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
    | getOccString v == "comb61" -> makeComb inports outports [t1, t2, t3, t4, t5, t6, t7] e
  App (App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) t6) e
    | getOccString v == "comb24" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | getOccString v == "comb33" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | getOccString v == "comb42" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
    | getOccString v == "comb51" -> makeComb inports outports [t1, t2, t3, t4, t5, t6] e
  App (App (App (App (App (App (Var v) t1) t2) t3) t4) t5) e
    | getOccString v == "comb14" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | getOccString v == "comb23" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | getOccString v == "comb32" -> makeComb inports outports [t1, t2, t3, t4, t5] e
    | getOccString v == "comb41" -> makeComb inports outports [t1, t2, t3, t4, t5] e
  App (App (App (App (App (Var v) t1) t2) t3) t4) e
    | getOccString v == "comb13" -> makeComb inports outports [t1, t2, t3, t4] e
    | getOccString v == "comb22" -> makeComb inports outports [t1, t2, t3, t4] e
    | getOccString v == "comb31" -> makeComb inports outports [t1, t2, t3, t4] e
  App (App (App (App (Var v) t1) t2) t3) e
    | getOccString v == "comb12" -> makeComb inports outports [t1, t2, t3] e
    | getOccString v == "comb21" -> makeComb inports outports [t1, t2, t3] e
  App (App (App (Var v) t1) t2) e
    | getOccString v == "comb11" -> makeComb inports outports [t1, t2]  e
  -- A delay only has a single parameterised type, and is therefore only
  -- specialised with one type application
  App (App (Var v) t) e
    | typeOrConstraint t && getOccString v == "delay" ->
        ( FunArg
        , map (\(t', i) -> (i, (t', CIR.EVar i))) (inports <> outports)
            <> zipWith (\i (t', _) -> (i, (t', delayExprToC e))) [ExId Delay] outports
        , delayBody
        )
  -- Might be a regular function, i.e. not a process
  e ->
    let (args, expr') = collectBinders e
        argMap = makeMap args inports
        (_, stmts, (_, expr)) = exprToCExpr 0 argMap (map fst inports) (fst . head $ outports) inports outports expr'
     in ( Return
        , argMap
        , CIR.SScope $
            stmts
              <> [CIR.SReturn . Just $ expr]
        )
  where
    -- The delay can both be used on intermediary signals and input/output
    -- signals. When used on an output signal, it needs to also output the
    -- current value of the delay, hence the shuffling of values.
    delayBody =
      CIR.SScope
        [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) (CIR.EDereference . CIR.EVar $ ExId Delay)
        , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Delay) (CIR.EDereference . CIR.EVar $ ExId Input <> Ix 0)
        ]

removePoint :: CIR.Type a -> CIR.Type a
removePoint = \case
  CIR.TPointer t -> t
  t -> t

vertexToExpr :: (Foldable t) => t (Id IdExt) -> (Vertex, CContext) -> CExpression
vertexToExpr pointers (Vertex{id = _, ..}, CContext {delayStorage}) = case process of
  Right _ -> undefined
  Left v -> CIR.ECall (const IEmpty <$> v) $ map ioToExpr (map Direct inputs) <> map ioToExpr (map Direct outputs) <> delayParams
 where
  delayParams =
    S.elems
      . S.map (\(_, s, _) -> case s of
        ExId Delay -> CIR.EVar . (<> ExId Delay) . Direct . head $ outputs
        _ -> CIR.EVar s)
      $ delayStorage
  ioToExpr io =
    if elem io pointers
      then CIR.EVar io
      else CIR.EReference . CIR.EVar $ io

instance Synthesizable CContext where
  synthesize procs p@Process{..} (newC, allC) =
    case filter (\CContext{from} -> binder == from) allC of
      -- We already synthesised this process, just return that
      c : _ -> (c : newC, allC)
      _ ->
        case subsystem of
          -- We don't have a subsystem, need to actually traverse the body.
          Nothing ->
            let inputs = zip (map portToC inports) inputIds
                outputs = zip (map portToC outports) outputIds
                (retLoc, argMap, body') = bodyToStatement inputs outputs body
                delay = length argMap > length inputs + length outputs
                argToDef (k, (t, _)) = (t, k)
                context =
                  CContext
                    { from = binder
                    , ret = case retLoc of
                        FunArg -> CIR.TVoid
                        Return -> fst . head $ outputs
                    , inputs = map argToDef . take (length inports) $ argMap
                    , outputs = case retLoc of
                        FunArg -> map argToDef . take (length outports) . drop (length inports) $ argMap
                        Return -> mempty
                    , delayStorage =
                        S.fromList
                          . map (\(i', (t', e')) -> (t', i', e'))
                          . drop (length inports + length outports)
                          $ argMap
                    , delay
                    , body = body'
                    , program = Nothing
                    }
             in (context : newC, context : allC)
          -- We have a subsystem, instantiate the scheduled vertices as calls
          -- to processes.
          Just System{..} ->
            let procs' = filter (/= p) procs
                -- Get all (unqiue) referenced processes in the system.
                systemProcs = S.elems . mconcat . map (vertexProcs (S.fromList procs)) $ vertices
                -- Synthesise all referenced processes.
                (subsysNew, allC1) = foldr (synthesize procs') (newC, allC) systemProcs
                inDefs = map varToCDef inputs
                outDefs = map varToCDef outputs
                -- Link all vertices to its invoked process' context.
                vertexContext v@Vertex {process} = case process of
                  Left i -> find (\CContext {from} -> from == i) subsysNew
                    >>= \c -> Just (v, c)
                  Right p' -> error $ "Encountered unlifted inline process: " <> show p'
                vContext = sequenceA $ map vertexContext vertices
                delays = filter (\(Vertex {delay}, _) -> delay) <$> vContext
                -- Get the vars of all delay signals.
                delaySigs =
                  mconcat
                    . mapMaybe
                      ( \Vertex{delay, outputs = outputs'} ->
                          if delay && length outputs' == 1
                            then Just outputs'
                            else Nothing
                      )
                    $ vertices
                delayTypes = map varToCDef delaySigs
                -- Get the definition of delay parameters and their initial value.
                delayDefs = mconcat . map (\(Vertex {outputs = outs}, CContext {delayStorage}) -> zipWith delayDef outs $ S.elems delayStorage) <$> delays
                delayDef var (t, i, e) = (t, Direct var <> i, e)
                -- Get all delays passed from subsystems.
                subsysStorage = mconcat . mapMaybe (\CContext{delayStorage, delay} -> if delay then Nothing else Just delayStorage) $ subsysNew
                findVert vid = find (\(Vertex{id = i}, _) -> i == vid) <$> vContext >>= id
                -- Collect the vertices in scheduled order
                schedVert = sequenceA <$> map findVert <$> schedule >>= id
                delaySigs' = map (\b -> Direct b <> ExId Delay) delaySigs
                pointers = delaySigs' <> map Direct inputs <> map Direct outputs
                -- Get the calls to the scheduled processes, passing which
                -- Ids should be dereferenced or not.
                schedStmts = map (CIR.SExpr . vertexToExpr pointers) <$> schedVert
                locals = S.filter (\v -> not (elem (Direct v) (pointers <> map Direct delaySigs))) . S.fromList . map (\(Edge v _ _) -> v) $ edges
                -- Get declarations of intermediare signals.
                localDefs = map ((\(t, s) -> CIR.SVarDecl t s Nothing) . (\(t, n) -> (removePoint t, n)) . varToCDef) . S.elems $ locals
                -- Get definitions of delays and initialise them to their
                -- previous value.
                delayTmps = map (\(t, i) -> CIR.SVarDef (removePoint t) i Nothing (CIR.EDereference . CIR.EVar $ i <> ExId Delay)) delayTypes
                context =
                  CContext
                    { from = binder
                    , ret = CIR.TVoid
                    , inputs = inDefs
                    , outputs = outDefs
                    , delay = False
                    , delayStorage = case delayDefs of
                        Just d -> S.fromList d <> subsysStorage
                        Nothing -> error "delay mismatch"
                    , body = CIR.SScope $ case schedStmts of
                        Just s -> localDefs <> delayTmps <> s
                        Nothing -> error "invalid schedule"
                    , program = Nothing
                    }
             in (context : newC, context : allC1)

  compose ([], _) = error "Missing main context"
  compose (mainC : _, allC) = mainC { program = Just $ CIR.Prog $ skepu <> [stdio] <> forwardDecls <> defs <> [main mainC] }
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
      CIR.TConstructor _ t' ->
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
      _ ->
        [ CIR.SVarAssign
            ret
            (CIR.ECall (ExId $ Name "scanf") [CIR.EString $ typeToFormat t, CIR.EReference $ CIR.EVar v])
        ]
    putOutput (t, v) = case removePoint t of
      CIR.TConstructor _ _ ->
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
      CIR.TLong -> "%ld"
      CIR.TFloat -> "%f"
      CIR.TDouble -> "%f"
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
    main CContext{..} =
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
    contextToGlobal CContext{..} =
      ( CIR.GFuncDeclare (Just CIR.Static) ret (const IEmpty <$> from) $
          inputs <> outputs <> (S.elems . S.map (\(t, n, _) -> (t, n))) delayStorage
      , CIR.GFuncDef
          (Just CIR.Static)
          ret
          (const IEmpty <$> from)
          (inputs <> outputs <> (S.elems . S.map (\(t, n, _) -> (t, n))) delayStorage)
          body
      )
