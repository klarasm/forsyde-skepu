{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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

import Data.List (elemIndex, find)
import Data.Maybe (mapMaybe)
import IR
import qualified CIR
import qualified Data.Set as S
import Prettyprinter

data (Show a, Show b) => Context a b = Context
  { from :: b
  , ret :: CIR.Type
  , inputs :: [(CIR.Type, String)]
  , outputs :: [(CIR.Type, String)]
  , delayStorage :: S.Set (CIR.Type, String, CIR.Expression)
  , body :: CIR.Statement
  }
  deriving (Show)
instance (Show a, Show b, Pretty a, Pretty b) => Pretty (Context a b) where
  pretty Context { .. } =
    pretty "Context"
      <> (nest 4 . tupled)
        [ pretty from
        , pretty ret
        , pretty inputs
        , pretty outputs
        , pretty . S.elems $ delayStorage
        , pretty body
        ]

class Synthesizable a b where
  -- may need to resolve a previously unresolved process as dependency
  synthesize :: [a] -> a -> ([Context a b], [Context a b]) -> ([Context a b], [Context a b])
  compose :: ([Context a b], [Context a b]) -> CIR.Program

portToC :: Port -> CIR.Type
portToC = \case
  Signal a _ _ -> portToC a
  Vector (Vector p _) _ ->
    CIR.TConstructor (CIR.TIdent "skepu::Matrix") (portToC p)
  Vector p _ ->
    CIR.TConstructor (CIR.TIdent "skepu::Vector") (portToC p)
  Opaque t -> typeToCType t

typeToCType :: Type -> CIR.Type
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

exprToCType = \case
  Type t -> typeToCType t
  Var v -> typeToCType . varType $ v
  _ -> error "Not a type!"

varToCDef :: Var -> (CIR.Type, String)
varToCDef v =
  let port = makePort . varType $ v
      ty = portToC port
      name = show $ Direct v
   in (ty, name)

argToCDef :: Var -> (CIR.Type, String)
argToCDef = (\(t, n) -> (CIR.TPointer t, n)) . varToCDef

getDelayExpr :: CoreExpr -> Maybe CoreExpr
getDelayExpr = \case
  App (App (Var v) _) e | isDelayVar v -> Just e
  _ -> Nothing

delayExprToC :: CoreExpr -> CIR.Expression
delayExprToC = \case
  App (Var _) (Lit (LitNumber _ i)) -> CIR.EInt . fromIntegral $ i
  _ -> undefined

vertexToExpr :: Foldable t => t Var -> [Context a Id] -> Vertex -> CIR.Expression
vertexToExpr pointers context Vertex { id = _, .. } = case process of
  Right _ -> undefined
  Left v -> CIR.ECall (show v) $ map ioToExpr inputs <> map ioToExpr outputs <> (delayParams v)
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
        then CIR.EVar . show $ Direct io
        else CIR.EReference . CIR.EVar . show $ Direct io

exprToCExpr' :: Integer -> [Var] -> CoreExpr -> (Integer, [CIR.Statement], CIR.Expression)
exprToCExpr' tmpix args expr = case expr of
  Lit (LitNumber _ i) -> (tmpix, [], CIR.EInt $ fromIntegral i)
  App _ (Lit (LitNumber _ i)) -> (tmpix, [], CIR.EInt $ fromIntegral i)
  Var v -> case varToArg args v of
    Just v' -> (tmpix, [], CIR.EDereference v')
    Nothing -> undefined
  -- Unary operator/function (with type variables)
  App (App (Var f) t) (Var v) | typeOrConstraint t && (not $ typeOrConstraint $ Var v) ->
    case varToArg args v of
      Just arg ->
         (tmpix, [], CIR.ECall (getOccString f) [arg])
      Nothing -> error $ "Var not in args! " <> showPprUnsafe expr
  -- A binary function passed as a value (with type constraints). Construct a lambda
  App (App (Var f) t1) t2 | typeOrConstraint t1 && typeOrConstraint t2 ->
    let in1 = "input_0"
        t1' = exprToCType t1
        in2 = "input_1"
        t2' = exprToCType t2
        (tmpix', stmts, expr') = resolveBinOp tmpix [] (CIR.EVar in1) (CIR.EVar in2) (getOccString f)
        expr'' = CIR.ELambda [] [(t1', in1), (t2', in2)] $ CIR.SScope [CIR.SReturn . Just $ expr']
     in (tmpix', stmts, expr'')
  -- Inner function (skeleton) applied to a function and var
  -- App (App (App (Var inner) t) f) (Var v) ->
  App (App (App (Var inner) t) f) (Var v) ->
    case varToArg args v of
      Just v' ->
        let (tmpix', stmts, exprToCall) = exprToCExpr' (tmpix+1) args f
            (tmpix'', toCall) = (tmpix'+1, "tmp_" <> show tmpix')
            stmt = CIR.SVarDef CIR.TAuto toCall $
              CIR.ECall (skelToSkePU $ getOccString inner) [CIR.EVar toCall]
         in
           (tmpix'', stmts <> [stmt], error $ show $ pretty stmt)
      Nothing -> undefined
  -- Binary operator/function (with type variables)
  App (App (App (App (Var f) t1) t2) e1) e2 | typeOrConstraint t1 && typeOrConstraint t2 ->
    let (tmpix1, stmts1, expr1) = exprToCExpr' tmpix args e1
        (tmpix2, stmts2, expr2) = exprToCExpr' tmpix1 args e2
     -- in resolveBinOp tmpix2 (stmts1 <> stmts2) expr1 expr2 $ s
     in resolveBinOp tmpix2 (stmts1 <> stmts2) expr1 expr2 $ getOccString f
  e -> error . showPprUnsafe $ e

skelToSkePU :: String -> String
skelToSkePU = \case
  "reduce" -> "skepu::Reduce"
  _ -> undefined

resolveBinOp ::
  Integer -> [CIR.Statement] -> CIR.Expression -> CIR.Expression -> String
  -> (Integer, [CIR.Statement], CIR.Expression)
resolveBinOp tmpix stmts expr1 expr2 = \case
  "+" -> (tmpix, stmts, CIR.EBinOp CIR.Add expr1 expr2)
  "*" -> (tmpix, stmts, CIR.EBinOp CIR.Multiply expr1 expr2)
  "-" -> (tmpix, stmts, CIR.EBinOp CIR.Subtract expr1 expr2)
  "quot" -> (tmpix, stmts, CIR.EBinOp CIR.Divide expr1 expr2)
  "div" -> error "Haskell `div` rounds to negative infinity, not implemented. Consider using `quot`"
  u -> error $ "Unknown function: " <> u

varToArg :: Eq a => [a] -> a -> Maybe CIR.Expression
varToArg args v =
  elemIndex v args >>= \ix -> pure . CIR.EVar $ "input_" <> show ix

exprToCExpr :: Integer -> [Var] -> CoreExpr -> (Integer, [CIR.Statement], CIR.Expression)
exprToCExpr counter args expr = case expr of
  App (App (App (Var f) _) _) (Var v) ->
    case varToArg args v of
      Just arg ->
         (counter, [], CIR.ECall (getOccString f) [arg])
      Nothing -> error "Var not in args!"
  App (App (Var f) t1) t2 | typeOrConstraint t1 && typeOrConstraint t2 ->
    let v1 = CIR.EVar "input_0"
        v2 = CIR.EVar "input_1"
        dv1 = CIR.EDereference v1
        dv2 = CIR.EDereference v2
     in resolveBinOp counter [] dv1 dv2 $ getOccString f
  e -> exprToCExpr' counter args e

bodyToStatement :: CoreExpr -> CIR.Statement
bodyToStatement = \case
  App (App (App (App (App (App (App (App (App (Var v) _) _) _) _) _) _) _) _) e ->
    error $ "9App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (App (Var v) _) _) _) _) _) _) _) e ->
    error $ "8App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (App (Var v) _) _) _) _) _) _) e ->
    error $ "7App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (App (App (App (App (Var v) _) _) _) _) _) e ->
    error $ "6App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (App (App (App (Var v) _) _) _) _) e
    | getOccString v == "comb22" -> case e of
      Lam b1 (Lam b2 (App (App (App (App (Var v') _) _) e1) e2)) | getOccString v' == "(,)" ->
        let (cntr, init1, ea1) = exprToCExpr 0 [b1, b2] e1
            (_, init2, ea2) = exprToCExpr cntr [b1, b2] e2
         in
          CIR.SScope $
            init1 <> init2 <>
            [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") ea1
            , CIR.SAssign (CIR.EDereference $ CIR.EVar "output_1") ea2
            ]
      e' -> error . showPprUnsafe $ e'
    | otherwise ->
      error $ "5App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (App (App (Var v) _) _) _) e
    | getOccString v == "comb21" -> case e of
      Lam b1 (Lam b2 e1) ->
        let (_, init1, ea1) = exprToCExpr 0 [b1, b2] e1
         in
          CIR.SScope $
            init1 <>
            [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") ea1
            ]
      e1 ->
        let (_, init1, ea1) = exprToCExpr 0 [] e1
         in
          CIR.SScope $
            init1 <>
            [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") $ ea1
            ]
    | getOccString v == "comb12" -> case e of
      Lam b1 (App (App (App (App (Var v') _) _) e1) e2) | getOccString v' == "(,)" ->
        let (cntr, init1, ea1) = exprToCExpr 0 [b1] e1
            (_, init2, ea2) = exprToCExpr cntr [b1] e2
         in
          CIR.SScope $
            init1 <>
            init2 <>
            [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") $ ea1
            , CIR.SAssign (CIR.EDereference $ CIR.EVar "output_1") $ ea2
            ]
      e' -> error . showPprUnsafe $ e'
    | otherwise ->
      error $ "4App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (App (Var v) _) _) e
    | getOccString v == "comb11" -> case e of
      Lam b1 e1 ->
        let (_, init1, ea1) = exprToCExpr 0 [b1] e1
         in
          CIR.SScope $
            init1 <>
            [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") ea1
            ]
      e1 ->
        let (_, init1, ea1) = exprToCExpr 0 [] e1
         in
          CIR.SScope $
            init1 <>
            [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") $ ea1
            ]
    | otherwise ->
      error $ "3App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (App (Var v) _) e
    | getOccString v == "delay" -> CIR.SScope
      [ CIR.SAssign (CIR.EDereference $ CIR.EVar "output_0") (CIR.EDereference $ CIR.EVar "input_0")
      ]
    | otherwise ->
      error $ "2App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  App (Var v) e ->
    error $ "1App(" <> show (Direct v) <> "): " <> showPprUnsafe e
  e -> error . showPprUnsafe $ e

instance Synthesizable Process Id where
  synthesize procs p@Process { .. } (newC, allC) =
    case filter (\Context { from } -> binder == from) allC of
    c : _ -> (c : newC, allC)
    _ ->
      case subsystem of
        Nothing ->
          let inDefs = zip (map (CIR.TPointer . portToC) inports) $ map (("input_"<>) . show) [0 :: Int ..]
              outDefs = zip (map (CIR.TPointer . portToC) outports) $ map (("output_"<>) . show) [0 :: Int ..]
              context = Context
                { from = binder
                , ret = CIR.TVoid
                , inputs = inDefs
                , outputs = outDefs
                , delayStorage = mempty
                , body = bodyToStatement body
                }
           in (context : newC, context : allC)
        Just System { .. } ->
          let procs' = filter (/=p) procs
              systemProcs = S.elems . mconcat . map (vertexProcs (S.fromList procs)) $ vertices
              (subsysNew, allC1) = foldr (synthesize procs') (newC, allC) systemProcs
              inDefs = map argToCDef inputs
              outDefs = map argToCDef outputs
              delays = mapMaybe (delayVertex procs) vertices
              delayProcs = mconcat . map (delayProc procs) $ delays
              delayBodies = sequence . map (getDelayExpr . \Process { body = b } -> b) $ delayProcs
              delayExprs = map delayExprToC <$> delayBodies
              delaySigs =
                mconcat
                  . map
                    ( \v@Vertex {outputs = outputs'} ->
                        if length outputs == 1
                          then outputs'
                          else error $ "invalid delay outputs: " <> show v
                    )
                  $ delays
              delayTypes = map argToCDef delaySigs
              delayDefs = delayExprs >>= \_c -> Just $ ((\(a, b) c -> (a, b, c)) <$> delayTypes) <*> _c
              subsysStorage = mconcat . map (\Context { delayStorage } -> delayStorage) $ subsysNew
              findVert vid = find (\Vertex { id = i } -> i == vid) vertices
              schedVert = mapMaybe findVert <$> schedule
              pointers = delaySigs <> inputs <> outputs
              schedStmts = map (CIR.SExpr . vertexToExpr pointers subsysNew) <$> schedVert
              locals = filter (\v -> not (elem v pointers)) . map (\(Edge v _ _) -> v) $ edges
              localDefs = map ((\(t, s) -> CIR.SVarDecl t s) . varToCDef) locals
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
  compose (mainC, allC) = CIR.Prog $ [stdio] <> forwardDecls <> defs <> map main mainC
    where
      (forwardDecls, defs) = unzip . map contextToGlobal $ allC
      stdio = CIR.GMacro "include" ["<stdio.h>"]
      removePoint = \case
        CIR.TPointer t -> t
        t -> t
      getInput ret (t, v) = CIR.SVarAssign ret (CIR.ECall "scanf" [CIR.EString $ typeToFormat t, CIR.EReference $ CIR.EVar v])
      putOutput (t, v) = CIR.SExpr $ CIR.ECall "printf" [CIR.EString $ typeToFormat t <> "\\n", CIR.EVar v]
      typeToFormat ty = case removePoint ty of
        CIR.TInt -> "%d"
        CIR.TFloat -> "%f"
        CIR.TChar -> "%c"
        t -> error $ "unknown format string for " <> show t
      getArg (_, v) = CIR.EReference $ CIR.EVar v
      statusVar = "status"
      main Context{..} =
        CIR.GFuncDef
          Nothing
          CIR.TInt
          "main"
          [(CIR.TInt, "argc"), (CIR.TPointer $ CIR.TPointer $ CIR.TChar, "argv")]
          $ CIR.SScope
          $ map (\(t, v, e) -> CIR.SVarDef (removePoint t) v e) (S.elems delayStorage)
            <> [ CIR.SWhile (CIR.EInt 1) $
                   CIR.SScope $
                     map (\(t, v) -> CIR.SVarDecl (removePoint t) v) (inputs <> outputs)
                       <> [CIR.SVarDecl CIR.TInt statusVar]
                       <> map (getInput statusVar) inputs
                       <> [ CIR.SIf
                              (CIR.EBinOp CIR.Less (CIR.EVar statusVar) (CIR.EInt 1))
                              (CIR.SScope [CIR.SBreak])
                              Nothing
                          ]
                       <> [ CIR.SExpr $
                              CIR.ECall (show from) $
                                map getArg $
                                  inputs <> outputs <> (map (\(t, v, _) -> (t, v)) $ S.elems delayStorage)
                          ]
                       <> map putOutput outputs
               ]
            <> [CIR.SReturn $ Just $ CIR.EInt $ -1]
      contextToGlobal Context { .. } =
        ( CIR.GFuncDeclare (Just CIR.Static) CIR.TVoid (show from) $
          inputs <> outputs <> (map (\(t, n, _) -> (t, n)) . S.elems) delayStorage
        , CIR.GFuncDef (Just CIR.Static) CIR.TVoid (show from)
            (inputs <> outputs <> (map (\(t, n, _) -> (t, n)) . S.elems) delayStorage)
            body
        )
