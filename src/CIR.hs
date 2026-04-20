{-# LANGUAGE LambdaCase #-}
module CIR (
  StorageClass (..),
  TypeQualifier (..),
  UnaryOperator (..),
  BinaryOperator (..),
  Type (..),
  Expression (..),
  Statement (..),
  Global (..),
  Program (..),
)
where

import Prettyprinter

data StorageClass
  = Auto
  | Register
  | Static
  | Extern
  | TypeDefinition
  deriving (Eq, Ord)
instance Show StorageClass where
  show = \case
    Auto -> "auto"
    Register -> "register"
    Static -> "static"
    Extern -> "extern"
    TypeDefinition -> "typedef"
instance Pretty StorageClass where
  pretty = unsafeViaShow

data TypeQualifier
  = Const
  | Restrict
  | Volatile
  deriving (Eq, Ord)
instance Show TypeQualifier where
  show = \case
    Const -> "const"
    Restrict -> "restrict"
    Volatile -> "volatile"
instance Pretty TypeQualifier where
  pretty = unsafeViaShow

data UnaryOperator
  = Negate
  | LogicalNot
  | PostIncrement
  | PostDecrement
  deriving (Eq, Ord)
instance Show UnaryOperator where
  show = \case
    Negate -> "-"
    LogicalNot -> "!"
    PostIncrement -> "++"
    PostDecrement -> "--"
instance Pretty UnaryOperator where
  pretty = unsafeViaShow

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
  deriving (Eq, Ord)
instance Show BinaryOperator where
  show = \case
    Add -> "+"
    Subtract -> "-"
    Multiply -> "*"
    Divide -> "/"
    Modulo -> "%"
    PlusAssign -> "+="
    MinusAssign -> "-="
    MultiplyAssign -> "*="
    DivideAssign -> "/="
    ModuloAssign -> "%="
    Equal -> "=="
    NotEqual -> "!="
    LogicalAnd -> "&&"
    LogicalOr -> "||"
    Less -> "<"
    LessEqual -> "<="
    Greater -> ">"
    GreaterEqual -> ">="
instance Pretty BinaryOperator where
  pretty = unsafeViaShow

data Type
  = TVoid
  | TInt
  | TFloat
  | TChar
  | TIdent String
  | TPointer Type
  | TReference Type
  | TFunctionPointer Type [Type]
  | TQualifiedType [TypeQualifier] Type
  | TConstructor Type Type
  | TAuto
  deriving (Eq, Ord, Show)

data Expression
  = EVar String
  | EInt Int
  | EChar Char
  | EString String
  | EBinOp BinaryOperator Expression Expression
  | EUnOp UnaryOperator Expression
  | ECall String [Expression]
  | ECallExpr Expression [Expression]
  | EArrayAccess Expression Expression
  | EReference Expression
  | EDereference Expression
  | EMemberAccess Expression String
  | EPointerAccess Expression String
  | EParen Expression
  | EStatement [Statement] Expression
  | ELambda [String] [(Type, String)] Statement
  deriving (Eq, Ord, Show)

data Statement
  = SExpr Expression
  | SVarDecl Type String
  | SVarDef Type String Expression
  | SAssign Expression Expression
  | SVarAssign String Expression
  | SArrayDecl Type String [Expression]
  | SArrayAssign String Expression Expression
  | SScope [Statement]
  | SIf Expression Statement (Maybe Statement)
  | SWhile Expression Statement
  | SFor Statement Expression Statement Statement
  | SBreak
  | SReturn (Maybe Expression)
  | SGoto String
  | SLabel String
  deriving (Eq, Ord, Show)

data Global
  = GFuncDeclare (Maybe StorageClass) Type String [(Type, String)]
  | GFuncDef (Maybe StorageClass) Type String [(Type, String)] Statement
  | GVarDeclare Type String
  | GVarDef Type String Expression
  | GStruct String [(Type, String)]
  | GMacro String [String]
  deriving (Eq, Ord, Show)

data Program = Prog [Global]
  deriving (Eq, Ord, Show)

testProg = Prog
  [ GMacro "include" ["<stdio.h>"]
  , GMacro "define" ["PI", "3.14159265458979323846"]
  , GStruct "tf"
    [ (TInt, "a")
    , (TChar, "b")
    ]
  , GFuncDeclare Nothing TInt "foo" [(TInt, "")]
  , GFuncDef Nothing TInt "main" [(TInt, "argc"), (TPointer (TPointer TChar), "argv")] (SScope
    [ SVarDecl TInt "test"
    , SVarDef TAuto "fwef" (ECall "skepu::Map<2>" [])
    , SVarDef TAuto "fwef" (ECall "skepu::Reduce" [ELambda [] [(TInt, "a"), (TInt, "b")] (SScope [SReturn . Just $ EBinOp Add (EVar "a") (EVar "b")])])
    , SArrayDecl TChar "s" [(EInt 2), (EInt 3)]
    , SVarAssign "test" (EInt 1)
    , SVarAssign "test" $ ECall "foo" [EVar "test"]
    , SIf (EBinOp Less (EVar "test") (EInt 10)) (SExpr $ EUnOp PostIncrement $ EVar "test") (Just $ SExpr $ EUnOp PostDecrement $ EVar "test")
    , SIf (EBinOp Less (EVar "test") (EInt 10)) (SScope [SExpr $ EUnOp PostIncrement $ EVar "test"]) (Just $ SScope [SExpr $ EUnOp PostDecrement $ EVar "test"])
    ])
  ]

-- >>> pretty testProg
-- #include <stdio.h>
-- #define PI 3.14159265458979323846
-- struct tf {
--     int a;
--     char b;
-- };
-- int foo (int );
-- int main (int argc, char **argv)
-- {
--     int test;
--     auto fwef = skepu::Map<2>();
--     auto fwef = skepu::Reduce([](int a, int b){
--         return (a + b);
--     });
--     char s[2][3];
--     test = 1;
--     test = foo(test);
--     if ((test < 10))
--         (test++);
--     else
--         (test--);
--     if ((test < 10)) {
--         (test++);
--     } else {
--         (test--);
--     }
-- }

instance Pretty Type where
  pretty = \case
    TVoid -> pretty "void"
    TInt -> pretty "int"
    TFloat -> pretty "float"
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

instance Pretty Expression where
  pretty = \case
    EVar x -> pretty x
    EInt i -> pretty i
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
    EReference e -> pretty "&" <> pretty e
    EDereference e -> pretty "*" <> pretty e
    EMemberAccess e f -> pretty e <> pretty "." <> pretty f
    EPointerAccess e f -> pretty e <> pretty "->" <> pretty f
    EParen e -> parens $ pretty e
    EStatement s e -> parens . braces $
      line <> (indent 4 . vsep . map needsSemi $ s) <> pretty e <> semi <> line
    ELambda capture params body ->
      pretty capture
        <> parens (hsep . punctuate comma $ (map prettyParam params))
        <+> pretty body

instance Pretty Statement where
  pretty = \case
    SExpr e -> pretty e
    SVarDecl t@(TPointer _) n ->
      pretty t <> pretty n
    SVarDecl t n ->
      pretty t <+> pretty n
    SVarDef t@(TPointer _) n e ->
      pretty t <> pretty n <+> pretty "=" <+> pretty e
    SVarDef t n e ->
      pretty t <+> pretty n <+> pretty "=" <+> pretty e
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
      pretty "if" <> parens (pretty e)
        <> nestOrScope' s1
    SWhile expr bodyS ->
      pretty "while" <+> parens (pretty expr)
        <> nestOrScope' bodyS
    SFor initS expr updS bodyS ->
      pretty "for" <+> parens (pretty initS <> semi <+> pretty expr <> semi <+> pretty updS)
      <+> nestOrScope bodyS
    SBreak -> pretty "break"
    SReturn (Just e) -> pretty "return" <+> pretty e
    SReturn Nothing -> pretty "return"
    SGoto l -> pretty "goto" <+> pretty l
    SLabel l -> pretty l <> colon

nestOrScope :: Statement -> Doc ann
nestOrScope s = case s of
  SScope _ -> space <> needsSemi s <> space
  _ -> line <> (indent 4 . needsSemi $ s) <> line
nestOrScope' :: Statement -> Doc ann
nestOrScope' s = case s of
  SScope _ -> space <> needsSemi s
  _ -> line <> (indent 4 . needsSemi $ s)
needsSemi :: Statement -> Doc ann
needsSemi s = case s of
  SExpr _ -> pretty s <> semi
  SVarDecl _ _ -> pretty s <> semi
  SVarDef _ _ _ -> pretty s <> semi
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

instance Pretty Global where
  pretty global = case global of
    GFuncDeclare (Just storageClass) returnType funcId parameters ->
      pretty storageClass
        <+> pretty returnType
        <+> pretty funcId
        <+> (parens . hsep . punctuate comma . map prettyParam) parameters
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
      <+> braces (line
          <> (indent 4 . vsep . map (<> semi) . map prettyParam) fields
          <> line)
          <> semi
    GMacro macro opt ->
      pretty "#" <> pretty macro <+> (hsep . map pretty) opt

prettyParam :: Pretty a => (Type, a) -> Doc ann
prettyParam (t@(TPointer _), i) = pretty t <> pretty i
prettyParam (t, i) = pretty t <+> pretty i

instance Pretty Program where
  pretty (Prog globals) =
    vsep . map pretty $ globals
