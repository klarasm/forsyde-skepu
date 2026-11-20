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
import GHC.Core.TyCo.Compare
import GHC.Core.TyCo.Rep
import GHC.Core.Type
import GHC.Types.Literal
import GHC.Types.Name (getOccString)
import GHC.Utils.Outputable (showPprUnsafe)

import Data.List (find, sort)
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified ForSyDe.Atom.Synthesis.CIR as CIR
import ForSyDe.Atom.Synthesis.IR as IR
import Prettyprinter

data IdExt
  = Name String
  | Input
  | Output
  | IDelay
  | Tmp
  | IVector
  | IMatrix
  | IEmpty
  | IReduce
  | Map
  deriving (Eq, Ord, Show)

instance Pretty IdExt where
  pretty (Name s) = pretty s
  pretty Input = pretty "input"
  pretty Output = pretty "output"
  pretty IDelay = pretty "delay"
  pretty Tmp = pretty "tmp"
  pretty IVector = pretty "skepu::Vector"
  pretty IMatrix = pretty "skepu::Matrix"
  pretty IEmpty = mempty
  pretty IReduce = pretty "skepu::Reduce"
  pretty Map = pretty "skepu::Map"

type CType = CIR.Type CId
type CExpression = CIR.Expression CId
type CStatement = CIR.Statement CId
type CProgram = CIR.Program CId
type CId = Id IdExt
type CDecl = (CType, CId)
type CArg = (CId, (CType, CExpression))

data CContext = CContext
  { from :: Id ()
  , ret :: CType
  , inputs :: [CDecl]
  , outputs :: [CDecl]
  , delayStorage :: S.Set CArg
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

typeStringToCType :: String -> CIR.Type a
typeStringToCType = \case
  "Int" -> CIR.TLong
  "Integer" -> CIR.TLong
  "Float" -> CIR.TFloat
  "Double" -> CIR.TDouble
  t -> error $ "Unknown type: " <> t

-- | Map GHC types into C types
typeToCType :: Type -> CType
typeToCType = \case
  TyVarTy v -> typeStringToCType $ getOccString v
  TyConApp v [] -> typeStringToCType $ getOccString v
  TyConApp v1 [v2]
    | getOccString v1 == "Num" -> case v2 of
        TyVarTy v2' -> typeStringToCType $ getOccString v2'
        TyConApp v2' _ -> typeStringToCType $ getOccString v2'
        _ -> error $ "Unknown type: " <> showPprUnsafe v1
    | getOccString v1 == "Ord" -> case v2 of
        TyVarTy v2' -> typeStringToCType $ getOccString v2'
        TyConApp v2' _ -> typeStringToCType $ getOccString v2'
        _ -> error $ "Unknown type: " <> showPprUnsafe v1
  TyConApp v1 _ | getOccString v1 == "Floating" -> CIR.TFloat
  TyConApp v1 _ | getOccString v1 == "Fractional" -> CIR.TFloat
  TyConApp v1 _ | getOccString v1 == "Integral" -> CIR.TLong
  t -> error $ "Unknown type: " <> showPprUnsafe t

-- | Make a C type of a GHC var
varToCType :: Var -> CType
varToCType = portToC . makePort . varType

{- | Make a C type of a GHC Core expression.
NOTE: should only be used on GHC types or vars
-}
exprToCType :: CoreExpr -> CType
exprToCType = \case
  Type t -> portToC . makePort $ t
  Var v -> varToCType v
  _ -> error "Not a type!"

-- | Make a C type and Id pair from a GHC Core binder
varToCDef :: Var -> CDecl
varToCDef v =
  let ty = varToCType v
      name = Direct v
   in (ty, name)

inputIds :: [CId]
inputIds = map ((ExId Input <>) . Ix) [0 ..]
inputArgs :: [CExpression]
inputArgs = map CIR.EVar inputIds
outputIds :: [CId]
outputIds = map ((ExId Output <>) . Ix) [0 ..]
outputArgs :: [CExpression]
outputArgs = map CIR.EVar outputIds

-- | Make a new temporary identifier
mkTemp :: Int -> (Int, CId)
mkTemp ix = (ix + 1, ExId Tmp <> Ix ix)

data OutputLoc
  = FunArg
  | Return

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
  "exp" -> case t1 of
    CIR.TDouble -> (tmpix, stmts, (tout, CIR.ECall (ExId $ Name "exp") [e1]))
    CIR.TFloat -> (tmpix, stmts, (tout, CIR.ECall (ExId $ Name "expf") [e1]))
    _ -> error $ "Unsupported type for exp: " <> show t1
  "log" -> case t1 of
    CIR.TDouble -> (tmpix, stmts, (tout, CIR.ECall (ExId $ Name "log") [e1]))
    CIR.TFloat -> (tmpix, stmts, (tout, CIR.ECall (ExId $ Name "logf") [e1]))
    _ -> error $ "Inconsistent types for log: " <> show t1 <> " " <> show tout
  "fromIntegral" -> case (t1, tout) of
    (CIR.TLong, CIR.TDouble) ->
      (tmpix, stmts, (tout, CIR.ECast (tout) expr1))
    _ -> error $ "Unsupported type conversion fromIntegral " <> show t1 <> " to " <> show tout
  u -> error $ "Unknown unary function: " <> u
 where
  e1 = derefTo tout t1 expr1
resolveOp tmpix stmts [(t1, expr1), (t2, expr2)] tout = \case
  "+" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Add e1 e2))
  "*" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Multiply e1 e2))
  "-" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Subtract e1 e2))
  "quot" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  "/" -> (tmpix, stmts, (tout, CIR.EBinOp CIR.Divide e1 e2))
  -- see https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p3724r0.html
  "div" ->
    let v1 = derefTo CIR.TVoid t1 expr1
        v2 = derefTo CIR.TVoid t2 expr2
     in ( tmpix
        , stmts
        ,
          ( tout
          , CIR.EBinOp
              CIR.Subtract
              (CIR.EBinOp CIR.Divide v1 v2)
              ( CIR.EBinOp
                  CIR.LogicalAnd
                  (CIR.EBinOp CIR.Less (CIR.EBinOp CIR.BitwiseXor v1 v2) (CIR.EInt 0))
                  (CIR.EBinOp CIR.NotEqual (CIR.EBinOp CIR.Modulo v1 v2) (CIR.EInt 0))
              )
          )
        )
  "const" -> (tmpix, stmts, (tout, e1))
  "max" -> (tmpix, stmts, (tout, CIR.ETernary (CIR.EBinOp CIR.Greater e1 e2) e1 e2))
  "min" -> (tmpix, stmts, (tout, CIR.ETernary (CIR.EBinOp CIR.Less e1 e2) e1 e2))
  "**" -> case (t1, t2) of
    (CIR.TDouble, CIR.TDouble) -> (tmpix, stmts, (tout, CIR.ECall (ExId $ Name "pow") [e1, e2]))
    (CIR.TFloat, CIR.TFloat) -> (tmpix, stmts, (tout, CIR.ECall (ExId $ Name "powf") [e1, e2]))
    _ -> error $ "Unsupported types for **: " <> show t1 <> " " <> show t2
  u -> error $ "Unknown binary function: " <> u
 where
  e1 = derefTo tout t1 expr1
  e2 = derefTo tout t2 expr2
resolveOp _ _ _ _ = undefined

{- | Wrap a C expression into a lambda, returning that as a statement and the
expression to call it.
-}
exprToLambda :: Int -> [CArg] -> [CType] -> CType -> [CDecl] -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToLambda tmpix args tin tout inports e =
    let (b1, e1) = collectBinders e
        largsDef = map (\v -> (varToCType v, Direct v :: CId)) b1
        largs = makeMap [] largsDef
        args' = map (\(i1, (t, i2)) -> (i1, (removePoint t, i2))) args
        implicit = zip (drop (length largs) tin) inputIds
        implicitArgs = makeMap [] implicit
        (tmpix1, stmts1, (_, expr1)) = exprToCExpr (tmpix+1) (largs <> implicitArgs <> args') tin tout implicit Nothing e1
        inExpr = CIR.getVars expr1
        explicitIds = map (\(i, _) -> i) . filter (\(i, _) -> elem i inExpr) $ largs
        notInArgs = filter (not . flip elem explicitIds) . sort $ inExpr
        captured =
          filter (\(_, i) -> i `elem` notInArgs)
            . map (\(t, i) -> (removePoint t, i))
            $ drop (length largs + length implicit) inports
        inputs = largsDef <> implicit <> captured
        expr2 = CIR.ELambda [] inputs $ CIR.SScope [CIR.SReturn $ Just expr1]
     in (tmpix1, stmts1, (tout, expr2))

-- | Apply a skeleton instance to its arguments
skelAppToCExpr :: Int -> OutputLoc -> [CArg] -> [CStatement] -> [CType] -> CType -> [CDecl] -> CId -> CExpression -> Maybe CDecl -> (Int, [CStatement], (CType, CExpression))
skelAppToCExpr tmpix1 ret args stmts1 tin tout inports skel lam assign =
  let (tmpix2, outname) = case assign of
        Just i -> (tmpix1, i)
        Nothing -> (,) tout <$> mkTemp tmpix1
      (tmpix3, skelInstance) = mkTemp tmpix2
      inputs = zipWith3 derefTo tin (map fst inports) (map (snd . snd) args)
      ini = case (tout, inports, args) of
        (CIR.TConstructor (CIR.TIdent (ExId IVector)) _, (inty, _) : _, (_, (_, expr)) : _) ->
          Just
            [ CIR.ECallExpr
                ( CIR.EMemberAccess
                    (derefTo CIR.TVoid inty expr)
                    (ExId $ Name "size")
                )
                []
            ]
        (CIR.TConstructor (CIR.TIdent (ExId IMatrix)) _, (inty, _) : _, (_, (_, expr)) : _) ->
          Just
            [ CIR.ECallExpr
                ( CIR.EMemberAccess
                    (derefTo CIR.TVoid inty expr)
                    (ExId $ Name "size_i")
                )
                []
            , CIR.ECallExpr
                ( CIR.EMemberAccess
                    (derefTo CIR.TVoid inty expr)
                    (ExId $ Name "size_j")
                )
                []
            ]
        _ -> Nothing
      outDerefed = derefTo CIR.TVoid (fst outname) $ CIR.EVar . snd $ outname
      call =
        CIR.ECall skelInstance $
          case ret of
            FunArg -> [outDerefed] <> inputs
            Return -> inputs
      stmts =
        case assign of
          Nothing -> [uncurry CIR.SVarDecl outname ini]
          _ ->  case ini of
            Just ini' -> [CIR.SExpr $ CIR.ECallExpr (CIR.EMemberAccess outDerefed . ExId $ Name "init") ini']
            _ -> []
        <> [CIR.SVarDef CIR.TAuto skelInstance Nothing $ CIR.ECall skel [lam]]
        <> case ret of
          FunArg -> [CIR.SExpr call]
          Return -> []
   in ( tmpix3
      , stmts1 <> stmts
      , case ret of
          FunArg -> CIR.EVar <$> outname
          Return -> (tout, call)
      )

{- | Decompose applications to a base expression, types, argument expressions,
and argument vars
-}
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

-- | Decompose expression and extract types of the Var being applied
decomposeExprTy :: Expr CoreBndr -> (Expr CoreBndr, Maybe ([Type], [Type]), [Arg CoreBndr], [Expr CoreBndr], [Expr CoreBndr], [CoreBndr])
decomposeExprTy e = case decomposeExpr e of
  (base@(Var v), tys, exprs, vars) ->
    (base, Just $ extractTypes [] . varType $ v, tys, exprs <> map Var vars, exprs, vars)
  (base, tys, exprs, vars) ->
    (base, Nothing, tys, exprs <> map Var vars, exprs, vars)

{- | Traverse a GHC Core expression and transform it into a C expression (and
possibly statements).
-}
exprToCExpr :: Int -> [CArg] -> [CType] -> CType -> [CDecl] -> Maybe CDecl -> CoreExpr -> (Int, [CStatement], (CType, CExpression))
exprToCExpr tmpix args tin tout inports assign = \case
  -- Literals
  App _ (Lit (LitNumber _ i)) -> (tmpix, [], (CIR.TLong, CIR.EInt $ fromIntegral i))
  Lit (LitNumber _ i) -> (tmpix, [], (CIR.TLong, CIR.EInt $ fromIntegral i))
  App _ (Lit (LitFloat f)) -> (tmpix, [], (CIR.TFloat, CIR.EFloat $ fromRational f))
  Lit (LitFloat f) -> (tmpix, [], (CIR.TFloat, CIR.EFloat $ fromRational f))
  App _ (Lit (LitDouble f)) -> (tmpix, [], (CIR.TDouble, CIR.EDouble $ fromRational f))
  Lit (LitDouble f) -> (tmpix, [], (CIR.TDouble, CIR.EDouble $ fromRational f))
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
    case (decomposeExprTy e, extractProcessType e) of
      -- Reduce(i)
      (_, Skeleton _ (ReduceI port fun ini _)) ->
            let (tmpix1, stmts1, (_, eIni)) = exprToCExpr tmpix args [portToC port] tout inports Nothing (coreFromProcType ini)
                (tmpix2, stmts2, (_, lam)) = exprToLambda tmpix1 args [portToC port, portToC port] (portToC port) inports (coreFromProcType fun)
                (tmpix3, stmts3, (t2, e2)) = skelAppToCExpr tmpix2 Return args (stmts1 <> stmts2) tin tout inports (ExId IReduce) lam Nothing
             in case e2 of
                  CIR.ECall skelInstance _ ->
                    let stmts4 = [CIR.SExpr $ CIR.ECallExpr (CIR.EMemberAccess (CIR.EVar skelInstance) (ExId $ Name "setStartValue")) [eIni]]
                     in (tmpix3, stmts3 <> stmts4, (t2, e2))
                  _ -> undefined -- This should not happen, skelApptToCExpr will always pass a ECall
      -- All skeleton farm applications
      (_, Skeleton _ (Farm i _ ipo _ (Core argExpr) _)) ->
        let (tmpix1, stmts1, (_, lam)) = exprToLambda tmpix args (map portToC ipo) tout inports argExpr
         in skelAppToCExpr tmpix1 FunArg args stmts1 tin tout inports (ExId Map <> ExId (Name $ "<" <> show i <> ">")) lam assign
      -- Vector length (two parametrised types and one type constraint)
      ((Var inner, Just ([tv], [tvout]), [_, _, _], [e1], _, _), _) | not $ tv `eqType` tvout ->
        let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType e1) inports Nothing e1
         in resolveOp tmpix1 stmts1 [(t1', expr1)] tout $ getOccString inner
      -- A fully applied binary function (one parametrised type and one type constraint)
      ((Var inner, Just ([tv1, tv2], [tvout]), [t1, _], [e1, e2], _, _), _)  | tv1 `eqType` tvout && tv2 `eqType` tvout ->
        let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports Nothing e1
            (tmpix2, stmts2, (t2', expr2)) = exprToCExpr tmpix1 args tin (exprToCType t1) inports Nothing e2
         in resolveOp tmpix2 (stmts1 <> stmts2) [(t1', expr1), (t2', expr2)] tout $ getOccString inner
      -- A partially applied binary function (one parametrised type and one type constraint)
      ((Var inner, Just ([tv1, tv2], [tvout]), [t1, _], [e1], _, _), _) | tv1 `eqType` tvout && tv2 `eqType` tvout ->
        let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports Nothing e1
            v1 = derefTo (exprToCType t1) (fst . head $ inports) $ CIR.EVar $ ExId Input <> Ix 0
         in resolveOp tmpix1 stmts1 [(t1', expr1), (exprToCType t1, v1)] tout $ getOccString inner
      -- An unapplied binary function (one parametrised type and one type constraint)
      ((Var inner, Just ([tv1, tv2], [tvout]), [_, _], [], [], []), _) | tv1 `eqType` tvout && tv2 `eqType` tvout->
        resolveOp 0 [] (take 2 . map snd $ args) tout $ getOccString inner
      -- A fully applied unary function (one parametrised type)
      ((Var inner, Just ([tv], [tvout]), [t1], [e1], _, _), _) | tv `eqType` tvout ->
        let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports Nothing e1
         in resolveOp tmpix1 stmts1 [(t1', expr1)] tout $ getOccString inner
      -- A fully applied unary function (one parametrised type)
      ((Var inner, Just ([tv], [tvout]), [t1, _], [e1], _, _), _) | tv `eqType` tvout ->
        let (tmpix1, stmts1, (t1', expr1)) = exprToCExpr tmpix args tin (exprToCType t1) inports Nothing e1
         in resolveOp tmpix1 stmts1 [(t1', expr1)] tout $ getOccString inner
      -- An unapplied unary function (one parametrised type)
      ((Var inner, Just ([tv], [tvout]), [_], [], [], []), _) | tv `eqType` tvout ->
        resolveOp 0 [] (take 1 . map snd $ args) tout $ getOccString inner
      -- An unapplied unary function (one parametrised type, one constraint)
      ((Var inner, Just ([tv], [tvout]), [t1, _], [], [], []), _) | tv `eqType` tvout ->
        resolveOp 0 [] (take 1 . map snd $ args) (exprToCType t1) $ getOccString inner
      -- A fully applied unary function (two parametrised types and two type constraints. e.g. fromIntegral)
      ((Var inner, Just ([tv], [tvout]), [t1, t2, _, _], [e1], _, _), _) | not $ tv `eqType` tvout ->
        let (tmpix1, stmts1, (t1', e1')) = exprToCExpr tmpix args tin (exprToCType t1) inports Nothing e1
         in resolveOp tmpix1 stmts1 [(t1', e1')] (exprToCType t2) $ getOccString inner
      ((_, ty, _, _, _, _), _) -> error $ showPprUnsafe e <> " " <> showPprUnsafe ty

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

{- | Dereference (or form a reference of) an expression of `inty` until it
matches `outty`
-}
derefTo :: CIR.Type a1 -> CIR.Type a2 -> CIR.Expression a -> CIR.Expression a
derefTo outty inty = derefArg (needDeref (0 :: Int) (inty, outty))

-- | Make an argument map, from args if existent otherwise from ports
makeMap :: [CoreBndr] -> [(a2, Id a)] -> [(Id a, (a2, CIR.Expression (Id a)))]
makeMap args ports = fmap (fmap (CIR.EVar)) <$> updatePorts args ports

updatePorts :: [CoreBndr] -> [(a2, Id a)] -> [((Id a), (a2, Id a))]
updatePorts [] ports = map (\(ty, ident) -> (ident, (ty, ident))) ports
updatePorts args ports = zipWith (\b (t, _) -> (Direct b, (t, (Direct b)))) args ports

assignOutputs :: (a1  -> a2  -> Maybe CDecl  -> b2  -> (a4, [CStatement], (CType, CExpression))) -> (a1, [CStatement]) -> ((a2, b2), CDecl) -> (a4, [CStatement])
assignOutputs fun (cntr, stmts) ((tout, expr), outport@(ty, ident)) = (cntr1, stmts1) where
  (cntr1, init1, tyE1) = fun cntr tout (Just outport) expr
  assignTo = (derefTo CIR.TVoid ty $ CIR.EVar ident)
  assignFrom = (derefTo CIR.TVoid (fst tyE1) $ snd tyE1)
  stmts1 =
    stmts
      <> init1
      <> if assignTo /= assignFrom
        then [CIR.SAssign (derefTo CIR.TVoid ty $ CIR.EVar ident) (derefTo CIR.TVoid (fst tyE1) $ snd tyE1)]
        else []

-- | Create combNM process
makeComb ::
  Int -> Int ->
  [CDecl] -> [CDecl] ->
  [Port] -> [Port] ->
  ProcessType ->
  (OutputLoc, [CArg], [CArg], [CArg], CStatement)
makeComb _ _ inports outports liports loports pt =
  let (args, expr) = collectBinders . coreFromProcType $ pt
      newInPorts = updatePorts args inports
      argMap = fmap (fmap CIR.EVar) <$> newInPorts
      outArgs = makeMap [] outports
      tys' = map portToC liports
      assign tys cntr tout a e = exprToCExpr cntr argMap tys tout (map snd newInPorts) a e
   in case decomposeExpr expr of
        (Var v, touts, argExprs, [])
          | (isTupleConstructor . getResType . varType $ v) ->
          let tyE = zipWith (\ty e -> (exprToCType ty, e)) touts argExprs
              outParams = zip tyE outports
              (_, stmts) = foldl' (assignOutputs $ assign tys') (0, []) outParams
           in (FunArg, argMap, outArgs, [], CIR.SScope stmts)
        _ ->
          let tout1 = portToC $ last loports
              outParams = zip [(tout1, expr)] outports
              (_, stmts) = foldl' (assignOutputs $ assign tys') (0, []) outParams
           in (FunArg, argMap, outArgs, [], CIR.SScope stmts)

{- | Here all the process constructors are recognised and either passed to a
helper or processed dierectly
-}
bodyToStatement :: [CDecl] -> [CDecl] -> ProcessType -> (OutputLoc, [CArg], [CArg], [CArg], CStatement)
bodyToStatement inports outports = \case
  MoCProcess _ (Comb inputs outputs iports oports expr) -> makeComb inputs outputs inports outports iports oports expr
  MoCProcess _ (Delay port expr) ->
        let (_, _, (_, delayExpr)) = exprToCExpr 0 [] [portToC port] (portToC port) inports Nothing (coreFromProcType expr)
         in ( FunArg
            , makeMap [] inports
            , makeMap [] outports
            , [(ExId IDelay, (CIR.TPointer (portToC port), delayExpr))]
            , -- The delay can both be used on intermediary signals and input/output
              -- signals. When used on an output signal, it needs to also output the
              -- current value of the delay, hence the shuffling of values.
              CIR.SScope
                [ CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId Output <> Ix 0) (CIR.EDereference . CIR.EVar $ ExId IDelay)
                , CIR.SAssign (CIR.EDereference . CIR.EVar $ ExId IDelay) (CIR.EDereference . CIR.EVar $ ExId Input <> Ix 0)
                ]
            )
  p@(MoCProcess _ _) -> error $ "Unsupported: " <> show p
  p@(Pipe _ _ _ _ _ _) -> error $ "Unsupported: " <> show p
  Skeleton e _ -> func e
  -- Might be a regular function, i.e. not a process
  Core e -> func e
  where
   func e =
    let (args, expr') = collectBinders e
        argMap = makeMap args inports
        (_, stmts, (_, expr)) = exprToCExpr 0 argMap (map fst inports) (fst . head $ outports) inports Nothing expr'
     in ( Return
        , argMap
        , []
        , []
        , CIR.SScope $
            stmts
              <> [CIR.SReturn . Just $ expr]
        )

removePoint :: CIR.Type a -> CIR.Type a
removePoint = \case
  CIR.TPointer t -> t
  t -> t

vertexToExpr :: (Foldable t) => t CId -> (Vertex a, CContext) -> CExpression
vertexToExpr pointers (Vertex{id = ix, ..}, CContext{delayStorage}) = case process of
  Right _ -> undefined
  Left v -> CIR.ECall (IEmpty <$ v) $ map (ioToExpr . (IEmpty <$) . fst) (inputs <> outputs) <> delayParams
 where
  delayParams =
    S.elems
      . S.map
        ( \(s, _) ->
            if delay
              then CIR.EVar . (<> ExId IDelay <> Ix ix) . (IEmpty <$) . fst . head $ outputs
              else CIR.EVar s
        )
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
                (retLoc, argMap, outArgs, stateArgs, body') = bodyToStatement inputs outputs procType
                argToDef (k, (t, _)) = (t, k)
                context =
                  CContext
                    { from = binder
                    , ret = case retLoc of
                        FunArg -> CIR.TVoid
                        Return -> fst . head $ outputs
                    , inputs = map argToDef argMap
                    , outputs = case retLoc of
                        FunArg -> map argToDef outArgs
                        Return -> mempty
                    , delayStorage = S.fromList stateArgs
                    , delay = not . null $ stateArgs
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
                updateId f (i, (t, e)) = (f i, (t, f <$> e))
                -- Link all vertices to its invoked process' context.
                vertexContext v@Vertex{process, id = ix} = case process of
                  Left i ->
                    find (\CContext{from} -> from == i) subsysNew
                      >>= \c@CContext{delayStorage} -> Just (v, c{delayStorage = updateId (<> Ix ix) `S.map` delayStorage})
                  Right p' -> error $ "Encountered unlifted inline process: " <> show p'
                vContext = sequenceA $ map vertexContext vertices
                delays = filter (\(Vertex{delay}, _) -> delay) <$> vContext
                -- Get the vars of all delay signals.
                delaySigs = S.fromList $
                    mapMaybe
                      ( \Edge{binder = b, ..} ->
                          if delayEdge
                            then Just (portToC port, IEmpty <$ b, source)
                            else Nothing
                      )
                    $ edges
                -- Get the definition of delay parameters and their initial value.
                delayDefs =
                  mconcat
                    . map
                      ( \(Vertex{outputs = outs}, CContext{delayStorage}) ->
                          zipWith delayDef outs $
                            S.elems delayStorage
                      )
                    <$> delays
                delayDef var (i, (t, e)) = ((IEmpty <$ fst var) <> i, (t, e))
                -- Get all delays passed from subsystems.
                subsysStorage =
                  mconcat
                    . mapMaybe
                      ( \(_, CContext{delayStorage, delay}) ->
                          if delay then Nothing else Just delayStorage
                      )
                    <$> vContext
                findVert vid = find (\(Vertex{id = i}, _) -> i == vid) <$> vContext >>= id
                -- Collect the vertices in scheduled order
                schedVert = sequenceA <$> map findVert <$> schedule >>= id
                delaySigs' = S.map (\(t, b, _) -> (t, (IEmpty <$ b) <> ExId IDelay)) delaySigs
                pointers = delaySigs' <> (S.map (\v -> ((portToC . makePort . varType) v, Direct v)) $ S.fromList (inputs <> outputs))
                -- Get the calls to the scheduled processes, passing which
                -- Ids should be dereferenced or not.
                schedStmts = map (CIR.SExpr . vertexToExpr (S.map snd pointers)) <$> schedVert
                locals =
                  S.difference
                    ( S.fromList $
                        mapMaybe
                          ( \(Edge ident port delay _ _) ->
                              if delay then Nothing else Just (portToC port, IEmpty <$ ident)
                          )
                          edges
                    )
                    (pointers)
                -- Get declarations of intermediare signals.
                localDefs = S.map ((\(t, s) -> CIR.SVarDecl t s Nothing) . (\(t, n) -> (removePoint t, n))) locals
                -- Get definitions of delays and initialise them to their
                -- previous value.
                delayTmps =
                  S.map
                    ( \(t, i, s) ->
                        CIR.SVarDef (removePoint t) i Nothing (CIR.EDereference . CIR.EVar $ i <> ExId IDelay <> Ix s)
                    )
                    delaySigs
                context =
                  CContext
                    { from = binder
                    , ret = CIR.TVoid
                    , inputs = inDefs
                    , outputs = outDefs
                    , delay = False
                    , delayStorage = case (delayDefs, subsysStorage) of
                        (Just d, Just s) -> S.fromList d <> s
                        _ -> error "delay mismatch"
                    , body = CIR.SScope $ case schedStmts of
                        Just s -> S.elems localDefs <> S.elems delayTmps <> s
                        Nothing -> error "invalid schedule"
                    , program = Nothing
                    }
             in (context : newC, context : allC1)

  compose ([], _) = error "Missing main context"
  compose (mainC : _, allC) = mainC{program = Just $ CIR.Prog $ skepu <> [stdio] <> forwardDecls <> defs <> [main mainC]}
   where
    (forwardDecls, defs) = unzip . map contextToGlobal $ allC
    skepu =
      [ CIR.GMacro (ExId $ Name "ifdef") [ExId $ Name "__cplusplus"]
      , CIR.GMacro (ExId $ Name "include") [ExId $ Name "<skepu>"]
      , CIR.GMacro (ExId $ Name "include") [ExId $ Name "<skepu-lib/io.hpp>"]
      , CIR.GMacro (ExId $ Name "endif") []
      ]
    stdio = CIR.GMacro (ExId $ Name "include") [ExId $ Name "<stdio.h>"]
    initV irId sizes =
      CIR.SExpr $
        CIR.ECallExpr (CIR.EMemberAccess (CIR.EVar irId) (ExId $ Name "init")) (CIR.EVar <$> sizes)
    forShort countId maxExp =
      CIR.SFor
        (CIR.SVarDef CIR.TSizeT countId Nothing (CIR.EInt 0))
        (CIR.EBinOp CIR.Less (CIR.EVar countId) maxExp)
        (CIR.SExpr $ CIR.EUnOp CIR.PostIncrement (CIR.EVar $ countId))
    getInput failStmt ret (t, v) = case removePoint t of
      CIR.TConstructor (CIR.TIdent (ExId IVector)) t' ->
        [ CIR.SExpr $
            CIR.ECall (ExId $ Name "skepu::external") $
              [ CIR.ELambda [ExId $ Name "&"] [] $
                  CIR.SScope $
                    [ CIR.SVarDecl CIR.TSizeT (ExId Tmp <> Ix 0) Nothing
                    , CIR.SVarDecl t' (ExId Input) Nothing
                    ]
                      <> getInput (CIR.SReturn Nothing) statusVar (CIR.TSizeT, ExId Tmp <> Ix 0)
                      <> [ initV v [ExId Tmp <> Ix 0] ]
                      <> [ forShort (ExId Tmp <> Ix 1) (CIR.EVar $ ExId Tmp <> Ix 0) $ CIR.SScope $
                             getInput (CIR.SReturn Nothing) statusVar (t', ExId Input)
                               <> [ CIR.SAssign
                                      (CIR.ECall v [CIR.EVar (ExId Tmp <> Ix 1)])
                                      (CIR.EVar $ ExId Input)
                                  ]
                         ]
              , CIR.ECall (ExId $ Name "skepu::write") [CIR.EVar v]
              ]
          , breakInput CIR.SBreak
        ]
      CIR.TConstructor (CIR.TIdent (ExId IMatrix)) t' ->
        [ CIR.SExpr $
            CIR.ECall (ExId $ Name "skepu::external") $
              [ CIR.ELambda [ExId $ Name "&"] [] $
                  CIR.SScope $
                    [ CIR.SVarDecl CIR.TSizeT (ExId Tmp <> Ix 0) Nothing
                    , CIR.SVarDecl CIR.TSizeT (ExId Tmp <> Ix 1) Nothing
                    , CIR.SVarDecl t' (ExId Input) Nothing
                    ]
                      <> getInput (CIR.SReturn Nothing) statusVar (CIR.TSizeT, ExId Tmp <> Ix 0)
                      <> getInput (CIR.SReturn Nothing) statusVar (CIR.TSizeT, ExId Tmp <> Ix 1)
                      <> [ initV v $ (ExId Tmp <>) . Ix <$> [0, 1] ]
                      <> [ forShort (ExId Tmp <> Ix 2) (CIR.EVar $ ExId Tmp <> Ix 0) $ CIR.SScope
                             [ forShort (ExId Tmp <> Ix 3) (CIR.EVar $ ExId Tmp <> Ix 1) $ CIR.SScope
                                 $ getInput (CIR.SReturn Nothing) statusVar (t', ExId Input)
                                   <> [ CIR.SAssign
                                          (CIR.ECall v [CIR.EVar (ExId Tmp <> Ix 2), CIR.EVar (ExId Tmp <> Ix 3)])
                                          (CIR.EVar $ ExId Input)
                                      ]
                            ]
                         ]
              , CIR.ECall (ExId $ Name "skepu::write") [CIR.EVar v]
              ]
          , breakInput CIR.SBreak
        ]
      _ ->
        [ CIR.SVarAssign
            ret
            (CIR.ECall (ExId $ Name "scanf") [CIR.EString $ typeToFormat t, CIR.EReference $ CIR.EVar v])
        , breakInput failStmt
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
      CIR.TDouble -> "%lf"
      CIR.TChar -> "%c"
      CIR.TSizeT -> "%zu"
      t -> error $ "unknown format string for " <> show t
    getArg (_, v) = CIR.EReference $ CIR.EVar v
    statusVar = ExId $ Name "status"
    breakInput stmt =
      CIR.SIf
        (CIR.EBinOp CIR.Less (CIR.EVar statusVar) (CIR.EInt 1))
        (CIR.SScope [stmt])
        Nothing
    main CContext{..} =
      CIR.GFuncDef
        Nothing
        CIR.TInt
        (ExId $ Name "main")
        [(CIR.TInt, ExId $ Name "argc"), (CIR.TPointer . CIR.TPointer $ CIR.TChar, ExId $ Name "argv")]
        $ CIR.SScope
        $ map (\(v, (t, e)) -> CIR.SVarDef (removePoint t) v Nothing e) (S.elems delayStorage)
          <> [ CIR.SWhile (CIR.EInt 1) $
                 CIR.SScope $
                   map (\(t, v) -> CIR.SVarDecl (removePoint t) v Nothing) (inputs <> outputs)
                     <> [CIR.SVarDef CIR.TInt statusVar Nothing (CIR.EInt 1)]
                     <> (mconcat . map (getInput CIR.SBreak statusVar)) inputs
                     <> [ CIR.SExpr $
                            CIR.ECall (IEmpty <$ from) $
                              map getArg $
                                inputs <> outputs <> (S.elems $ S.map (\(v, (t, _)) -> (t, v)) $ delayStorage)
                        ]
                     <> (mconcat . map putOutput) outputs
             ]
          <> [CIR.SReturn $ Just $ CIR.EInt $ -1]
    contextToGlobal CContext{..} =
      ( CIR.GFuncDeclare (Just CIR.Static) ret (IEmpty <$ from) $
          inputs <> outputs <> (S.elems . S.map (\(n, (t, _)) -> (t, n))) delayStorage
      , CIR.GFuncDef
          (Just CIR.Static)
          ret
          (IEmpty <$ from)
          (inputs <> outputs <> (S.elems . S.map (\(n, (t, _)) -> (t, n))) delayStorage)
          body
      )
