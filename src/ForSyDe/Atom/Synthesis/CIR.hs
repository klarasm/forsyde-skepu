{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}

module ForSyDe.Atom.Synthesis.CIR (
  StorageClass (..),
  TypeQualifier (..),
  UnaryOperator (..),
  BinaryOperator (..),
  Type (..),
  Expression (..),
  Statement (..),
  Global (..),
  Program (..),
  getVars
)
where

import Prettyprinter
import Data.Data (Data, Typeable)

data StorageClass
  = Auto
  | Register
  | Static
  | Extern
  | TypeDefinition
  deriving (Data, Typeable, Eq, Ord)
instance Pretty StorageClass where
  pretty = \case
    Auto -> pretty "auto"
    Register -> pretty "register"
    Static -> pretty "static"
    Extern -> pretty "extern"
    TypeDefinition -> pretty "typedef"
instance Show StorageClass where
  show = show . pretty

data TypeQualifier
  = Const
  | Restrict
  | Volatile
  deriving (Data, Typeable, Eq, Ord)
instance Pretty TypeQualifier where
  pretty = \case
    Const -> pretty "const"
    Restrict -> pretty "restrict"
    Volatile -> pretty "volatile"
instance Show TypeQualifier where
  show = show . pretty

data UnaryOperator
  = Negate
  | LogicalNot
  | PostIncrement
  | PostDecrement
  deriving (Data, Typeable, Eq, Ord)
instance Pretty UnaryOperator where
  pretty = \case
    Negate -> pretty "-"
    LogicalNot -> pretty "!"
    PostIncrement -> pretty "++"
    PostDecrement -> pretty "--"
instance Show UnaryOperator where
  show = show . pretty

data BinaryOperator
  = Add
  | Subtract
  | Multiply
  | Divide
  | Modulo
  | PlusAssign
  | MinusAssign
  | MultiplyAssign
  | DivideAssign
  | ModuloAssign
  | Equal
  | NotEqual
  | LogicalAnd
  | LogicalOr
  | Less
  | LessEqual
  | Greater
  | GreaterEqual
  deriving (Data, Typeable, Eq, Ord)
instance Pretty BinaryOperator where
  pretty = \case
    Add -> pretty "+"
    Subtract -> pretty "-"
    Multiply -> pretty "*"
    Divide -> pretty "/"
    Modulo -> pretty "%"
    PlusAssign -> pretty "+="
    MinusAssign -> pretty "-="
    MultiplyAssign -> pretty "*="
    DivideAssign -> pretty "/="
    ModuloAssign -> pretty "%="
    Equal -> pretty "=="
    NotEqual -> pretty "!="
    LogicalAnd -> pretty "&&"
    LogicalOr -> pretty "||"
    Less -> pretty "<"
    LessEqual -> pretty "<="
    Greater -> pretty ">"
    GreaterEqual -> pretty ">="
instance Show BinaryOperator where
  show = show . pretty

data Type a
  = TVoid
  | TInt
  | TLong
  | TSizeT
  | TFloat
  | TDouble
  | TChar
  | TIdent a
  | TPointer (Type a)
  | TReference (Type a)
  | TFunctionPointer (Type a) [(Type a)]
  | TQualifiedType [TypeQualifier] (Type a)
  | TConstructor (Type a) (Type a)
  | TAuto
  deriving (Data, Typeable, Eq, Ord, Show)
instance Functor Type where
  fmap f = \case
    TVoid -> TVoid
    TInt -> TInt
    TLong -> TLong
    TSizeT -> TSizeT
    TFloat -> TFloat
    TDouble -> TDouble
    TChar -> TChar
    TIdent n -> TIdent (f n)
    TPointer t -> TPointer (f <$> t)
    TReference t -> TReference (f <$> t)
    TFunctionPointer retTy argTy -> TFunctionPointer (f <$> retTy) (map (fmap f) argTy)
    TQualifiedType qual t -> TQualifiedType qual (f <$> t)
    TConstructor constrTy innerTy -> TConstructor (f <$> constrTy) (f <$> innerTy)
    TAuto -> TAuto

data Expression a
  = EVar a
  | EInt Int
  | EFloat Float
  | EChar Char
  | EString String
  | EBinOp BinaryOperator (Expression a) (Expression a)
  | EUnOp UnaryOperator (Expression a)
  | ECall a [(Expression a)]
  | ECallExpr (Expression a) [(Expression a)]
  | EArrayAccess (Expression a) (Expression a)
  | EReference (Expression a)
  | EDereference (Expression a)
  | EMemberAccess (Expression a) (a)
  | EPointerAccess (Expression a) (a)
  | EParen (Expression a)
  | EStatement [(Statement a)] (Expression a)
  | ELambda [(a)] [((Type a), (a))] (Statement a)
  | ETernary (Expression a) (Expression a) (Expression a)
  | ECast (Type a) (Expression a)
  deriving (Data, Typeable, Eq, Ord, Show)
instance Functor Expression where
  fmap f = \case
    EVar i -> EVar $ f i
    EInt l -> EInt l
    EFloat l -> EFloat l
    EChar c -> EChar c
    EString s -> EString s
    EBinOp op e1 e2 -> EBinOp op (f <$> e1) (f <$> e2)
    EUnOp op e -> EUnOp op (f <$> e)
    ECall name args -> ECall (f name) (map (fmap f) args)
    ECallExpr name args -> ECallExpr (f <$> name) (map (fmap f) args)
    EArrayAccess name ix -> EArrayAccess (f <$> name) (f <$> ix)
    EReference e -> EReference $ f <$> e
    EDereference e -> EDereference $ f <$> e
    EMemberAccess name field -> EMemberAccess (f <$> name) (f field)
    EPointerAccess name field -> EPointerAccess (f <$> name) (f field)
    EParen e -> EParen (f <$> e)
    EStatement stmts expr -> EStatement (map (fmap f) stmts) (f <$> expr)
    ELambda capture parms stmt -> ELambda (map f capture) (map (parmFmap f) parms) (f <$> stmt)
    ETernary cond true false -> ETernary (f <$> cond) (f <$> true) (f <$> false)
    ECast t e -> ECast (f <$> t) (f <$> e)

data Statement a
  = SExpr (Expression a)
  | SVarDecl (Type a) a (Maybe [Expression a])
  | SVarDef (Type a) a (Maybe [Expression a]) (Expression a)
  | SAssign (Expression a) (Expression a)
  | SVarAssign (a) (Expression a)
  | SArrayDecl (Type a) a [(Expression a)]
  | SArrayAssign a (Expression a) (Expression a)
  | SScope [(Statement a)]
  | SIf (Expression a) (Statement a) (Maybe (Statement a))
  | SWhile (Expression a) (Statement a)
  | SFor (Statement a) (Expression a) (Statement a) (Statement a)
  | SBreak
  | SReturn (Maybe (Expression a))
  | SGoto a
  | SLabel a
  | SStream a Bool [Expression a]
  deriving (Data, Typeable, Eq, Ord, Show)
instance Functor Statement where
  fmap f = \case
    SExpr e -> SExpr (f <$> e)
    SVarDecl t n ini -> SVarDecl (f <$> t) (f n) (map (fmap f) <$> ini)
    SVarDef t n ini e -> SVarDef (f <$> t) (f n) (map (fmap f) <$> ini) (f <$> e)
    SAssign evar expr -> SAssign (f <$> evar) (f <$> expr)
    SVarAssign v expr -> SVarAssign (f v) (f <$> expr)
    SArrayDecl t n dim -> SArrayDecl (f <$> t) (f n) (map (fmap f) dim)
    SArrayAssign n ix expr -> SArrayAssign (f n) (f <$> ix) (f <$> expr)
    SScope stmts -> SScope (map (fmap f) stmts)
    SIf cond ethen eelse -> SIf (f <$> cond) (f <$> ethen) (fmap (fmap f) eelse)
    SWhile cond body -> SWhile (f <$> cond) (f <$> body)
    SFor ini cond post body -> SFor (f <$> ini) (f <$> cond) (f <$> post) (f <$> body)
    SBreak -> SBreak
    SReturn ret -> SReturn $ fmap (fmap f) ret
    SGoto n -> SGoto $ f n
    SLabel n -> SLabel $ f n
    SStream n dir exprs -> SStream (f n) dir (map (fmap f) exprs)

data Global a
  = GFuncDeclare (Maybe StorageClass) (Type a) a [(Type a, a)]
  | GFuncDef (Maybe StorageClass) (Type a) (a) [(Type a, a)] (Statement a)
  | GVarDeclare (Type a) a
  | GVarDef (Type a) a (Expression a)
  | GStruct a [(Type a, a)]
  | GMacro a [a]
  deriving (Data, Typeable, Eq, Ord, Show)
instance Functor Global where
  fmap f = \case
    GFuncDeclare sc t n parms -> GFuncDeclare sc (f <$> t) (f n) (map (parmFmap f) parms)
    GFuncDef sc t n parms stmt -> GFuncDef sc (f <$> t) (f n) (map (parmFmap f) parms) (f <$> stmt)
    GVarDeclare t n -> GVarDeclare (f <$> t) (f n)
    GVarDef t n e -> GVarDef (f <$> t) (f n) (f <$> e)
    GStruct n membs -> GStruct (f n) (map (parmFmap f) membs)
    GMacro n args -> GMacro (f n) (map f args)

parmFmap :: Functor f => (a -> b) -> (f a, a) -> (f b, b)
parmFmap f (t, n) = (f <$> t, f n)

data Program a = Prog [Global a]
  deriving (Data, Typeable, Eq, Ord, Show)
instance Functor Program where
  fmap f (Prog globs) = Prog $ map (fmap f) globs

instance (Pretty a) => Pretty (Type a) where
  pretty = \case
    TVoid -> pretty "void"
    TInt -> pretty "int"
    TLong -> pretty "long"
    TSizeT -> pretty "size_t"
    TFloat -> pretty "float"
    TDouble -> pretty "double"
    TChar -> pretty "char"
    TIdent s -> pretty s
    TPointer t@(TPointer _) -> pretty t <> pretty "*"
    TPointer t -> pretty t <+> pretty "*"
    TReference t -> pretty t <> pretty "&"
    TQualifiedType quals ty -> hsep (map pretty quals) <+> pretty ty
    TFunctionPointer ret args ->
      pretty ret <+> pretty "(*)"
        <> parens
          ( case args of
              [] -> pretty "void"
              _ -> hsep . punctuate comma . map pretty $ args
          )
    TConstructor con inner -> pretty con <> angles (pretty inner)
    -- Note: for plain C __auto_type would be better, but SKePU is C++ and c++
    -- does not recognize __auto_type. In C23 and later auto has the same
    -- meaning as __auto_type and thus similar to C++ auto.
    TAuto -> pretty "auto"

instance (Pretty a) => Pretty (Expression a) where
  pretty = \case
    EVar x -> pretty x
    EInt i -> pretty i
    EFloat f -> pretty f
    EChar c -> squotes . pretty $ c
    EString s -> dquotes . pretty $ s
    EBinOp op e1 e2 ->
      parens $ pretty e1 <+> pretty op <+> pretty e2
    EUnOp op@PostIncrement e -> parens $ pretty e <> pretty op
    EUnOp op@PostDecrement e -> parens $ pretty e <> pretty op
    EUnOp op e -> parens $ pretty op <> pretty e
    ECall fun args ->
      pretty fun <> (parens . hsep . punctuate comma . map pretty $ args)
    ECallExpr e args ->
      pretty e <> (parens . hsep . punctuate comma . map pretty $ args)
    EArrayAccess e i -> pretty e <> brackets (pretty i)
    EReference e -> pretty "&" <> (parens . pretty) e
    EDereference e -> pretty "*" <> (parens . pretty) e
    EMemberAccess e f -> (parens . pretty) e <> pretty "." <> pretty f
    EPointerAccess e f -> (parens . pretty) e <> pretty "->" <> pretty f
    EParen e -> parens $ pretty e
    EStatement s e ->
      parens . braces $
        line <> (indent 4 . vsep . map needsSemi $ s) <> pretty e <> semi <> line
    ELambda capture params body ->
      pretty capture
        <> parens (hsep . punctuate comma $ (map prettyParam params))
          <+> pretty body
    ETernary cond true false ->
      lparen <> pretty cond <> rparen <+> pretty "?"
        <+> lparen <> pretty true <> rparen <+> colon
        <+> lparen <> pretty false <> rparen
    ECast ty expr -> parens (pretty ty) <> parens (pretty expr)

instance (Pretty a) => Pretty (Statement a) where
  pretty = \case
    SExpr e -> pretty e
    SVarDecl t@(TPointer _) n Nothing ->
      pretty t <> pretty n
    SVarDecl t@(TPointer _) n (Just ini) ->
      pretty t <> pretty n <> parens (hsep . punctuate comma . map pretty $ ini)
    SVarDecl t n (Just ini) ->
      pretty t <+> pretty n <> parens (hsep . punctuate comma . map pretty $ ini)
    SVarDecl t n Nothing ->
      pretty t <+> pretty n
    SVarDef t@(TPointer _) n Nothing e ->
      pretty t <> pretty n <+> pretty "=" <+> pretty e
    SVarDef t@(TPointer _) n (Just ini) e ->
      pretty t
        <> pretty n
        <> parens (hsep . punctuate comma . map pretty $ ini)
          <+> pretty "="
          <+> pretty e
    SVarDef t n Nothing e ->
      pretty t <+> pretty n <+> pretty "=" <+> pretty e
    SVarDef t n (Just ini) e ->
      pretty t <+> pretty n
        <> parens (hsep . punctuate comma . map pretty $ ini)
          <+> pretty "="
          <+> pretty e
    SAssign e1 e2 ->
      pretty e1 <+> pretty "=" <+> pretty e2
    SVarAssign n e ->
      pretty n <+> pretty "=" <+> pretty e
    SArrayDecl t n e ->
      pretty t <+> pretty n
        <> (hcat . map (brackets . pretty)) e
    SArrayAssign n i e ->
      pretty n <> brackets (pretty i) <+> pretty "=" <+> pretty e
    SScope stmts ->
      braces $ line <> (indent 4 . vsep . map needsSemi $ stmts) <> line
    SIf e s1 (Just s2) ->
      pretty "if" <+> parens (pretty e)
        <> nestOrScope s1
        <> pretty "else"
        <> nestOrScope' s2
    SIf e s1 Nothing ->
      pretty "if"
        <> parens (pretty e)
        <> nestOrScope' s1
    SWhile expr bodyS ->
      pretty "while" <+> parens (pretty expr)
        <> nestOrScope' bodyS
    SFor initS expr updS bodyS ->
      pretty "for"
        <+> parens (pretty initS <> semi <+> pretty expr <> semi <+> pretty updS)
        <> nestOrScope bodyS
    SBreak -> pretty "break"
    SReturn (Just e) -> pretty "return" <+> pretty e
    SReturn Nothing -> pretty "return"
    SGoto l -> pretty "goto" <+> pretty l
    SLabel l -> pretty l <> colon
    SStream n dir exprs -> pretty n <+> (hsep . map (sepIO dir)) (map pretty exprs)
     where
      sepIO d v = (if d then pretty "<<" else pretty ">>") <+> v

nestOrScope :: (Pretty a) => (Statement a) -> Doc ann
nestOrScope s = case s of
  SScope _ -> space <> needsSemi s <> space
  _ -> line <> (indent 4 . needsSemi $ s) <> line
nestOrScope' :: (Pretty a) => (Statement a) -> Doc ann
nestOrScope' s = case s of
  SScope _ -> space <> needsSemi s
  _ -> line <> (indent 4 . needsSemi $ s)
needsSemi :: (Pretty a) => (Statement a) -> Doc ann
needsSemi s = case s of
  SExpr _ -> pretty s <> semi
  SVarDecl _ _ _ -> pretty s <> semi
  SVarDef _ _ _ _ -> pretty s <> semi
  SAssign _ _ -> pretty s <> semi
  SVarAssign _ _ -> pretty s <> semi
  SArrayDecl _ _ _ -> pretty s <> semi
  SArrayAssign _ _ _ -> pretty s <> semi
  SScope _ -> pretty s
  SIf _ _ _ -> pretty s
  SWhile _ _ -> pretty s
  SFor _ _ _ _ -> pretty s
  SBreak -> pretty s <> semi
  SReturn _ -> pretty s <> semi
  SGoto _ -> pretty s <> semi
  SLabel _ -> pretty s
  SStream _ _ _ -> pretty s <> semi

instance (Pretty a) => Pretty (Global a) where
  pretty global = case global of
    GFuncDeclare (Just storageClass) returnType funcId parameters ->
      pretty storageClass
        <+> pretty returnType
        <+> pretty funcId
        <> (parens . hsep . punctuate comma . map prettyParam) parameters
        <> semi
    GFuncDeclare Nothing returnType funcId parameters ->
      pretty returnType
        <+> pretty funcId
        <+> (parens . hsep . punctuate comma . map prettyParam) parameters
        <> semi
    GFuncDef (Just storageClass) returnType funcId parameters body ->
      pretty storageClass
        <+> pretty returnType
        <+> pretty funcId
        <> (parens . hsep . punctuate comma . map prettyParam) parameters
        <> line
        <> pretty body
    GFuncDef Nothing returnType funcId parameters body ->
      pretty returnType
        <+> pretty funcId
        <+> (parens . hsep . punctuate comma . map prettyParam) parameters
        <> line
        <> pretty body
    GVarDeclare varType varId ->
      pretty varType <+> pretty varId
    GVarDef varType varId expression ->
      pretty varType
        <+> pretty varId
        <+> pretty "="
        <+> pretty expression
    GStruct structId fields ->
      pretty "struct"
        <+> pretty structId
        <+> braces
          ( line
              <> (indent 4 . vsep . map (<> semi) . map prettyParam) fields
              <> line
          )
        <> semi
    GMacro macro opt ->
      pretty "#" <> pretty macro <+> (hsep . map pretty) opt

prettyParam :: (Pretty a) => ((Type a), a) -> Doc ann
prettyParam (t@(TPointer _), i) = pretty t <> pretty i
prettyParam (t, i) = pretty t <+> pretty i

instance (Pretty a) => Pretty (Program a) where
  pretty (Prog globals) =
    vsep . map pretty $ globals

getVars :: Expression a -> [a]
getVars = go []
  where
    go acc = \case
      EVar v -> v : acc
      EBinOp _ e1 e2 -> go (go acc e1) e2
      EUnOp _ e -> go acc e
      ECall _ el -> foldr (flip go) acc el
      ECallExpr e el -> foldr (flip go) (go acc e) el
      EArrayAccess e1 e2 -> go (go acc e1) e2
      EReference e -> go acc e
      EDereference e -> go acc e
      EMemberAccess e _ -> go acc e
      EPointerAccess e _ -> go acc e
      EParen e -> go acc e
      ETernary e1 e2 e3 -> go (go (go acc e1) e2) e3
      -- EInt _ -> acc
      -- EFloat _ -> acc
      -- EChar _ -> acc
      -- EString _ -> acc
      -- EStatement _ _ -> acc
      -- ELambda _ _ _ -> acc
      _ -> acc
