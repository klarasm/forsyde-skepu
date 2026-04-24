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

import qualified IR
import Prettyprinter

data StorageClass
  = Auto
  | Register
  | Static
  | Extern
  | TypeDefinition
  deriving (Eq, Ord)
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
  deriving (Eq, Ord)
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
  deriving (Eq, Ord)
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
  deriving (Eq, Ord)
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
  | TSizeT
  | TFloat
  | TChar
  | TIdent (IR.Id a)
  | TPointer (Type a)
  | TReference (Type a)
  | TFunctionPointer (Type a) [(Type a)]
  | TQualifiedType [TypeQualifier] (Type a)
  | TConstructor (Type a) (Type a)
  | TAuto
  deriving (Eq, Ord, Show)

data Expression a
  = EVar (IR.Id a)
  | EInt Int
  | EFloat Float
  | EChar Char
  | EString String
  | EBinOp BinaryOperator (Expression a) (Expression a)
  | EUnOp UnaryOperator (Expression a)
  | ECall (IR.Id a) [(Expression a)]
  | ECallExpr (Expression a) [(Expression a)]
  | EArrayAccess (Expression a) (Expression a)
  | EReference (Expression a)
  | EDereference (Expression a)
  | EMemberAccess (Expression a) (IR.Id a)
  | EPointerAccess (Expression a) (IR.Id a)
  | EParen (Expression a)
  | EStatement [(Statement a)] (Expression a)
  | ELambda [(IR.Id a)] [((Type a), (IR.Id a))] (Statement a)
  deriving (Eq, Ord, Show)

data Statement a
  = SExpr (Expression a)
  | SVarDecl (Type a) (IR.Id a) (Maybe [Expression a])
  | SVarDef (Type a) (IR.Id a) (Maybe [Expression a]) (Expression a)
  | SAssign (Expression a) (Expression a)
  | SVarAssign (IR.Id a) (Expression a)
  | SArrayDecl (Type a) (IR.Id a) [(Expression a)]
  | SArrayAssign (IR.Id a) (Expression a) (Expression a)
  | SScope [(Statement a)]
  | SIf (Expression a) (Statement a) (Maybe (Statement a))
  | SWhile (Expression a) (Statement a)
  | SFor (Statement a) (Expression a) (Statement a) (Statement a)
  | SBreak
  | SReturn (Maybe (Expression a))
  | SGoto (IR.Id a)
  | SLabel (IR.Id a)
  | SStream (IR.Id a) Bool [Expression a]
  deriving (Eq, Ord, Show)

data Global a
  = GFuncDeclare (Maybe StorageClass) (Type a) (IR.Id a) [((Type a), (IR.Id a))]
  | GFuncDef (Maybe StorageClass) (Type a) (IR.Id a) [((Type a), (IR.Id a))] (Statement a)
  | GVarDeclare (Type a) (IR.Id a)
  | GVarDef (Type a) (IR.Id a) (Expression a)
  | GStruct (IR.Id a) [((Type a), (IR.Id a))]
  | GMacro (IR.Id a) [(IR.Id a)]
  deriving (Eq, Ord, Show)

data Program a = Prog [(Global a)]
  deriving (Eq, Ord, Show)

testProg :: Program String
testProg =
  Prog
    [ GMacro (IR.ExId "include") [IR.ExId "<stdio.h>"]
    , GMacro (IR.ExId "define") [IR.ExId "PI", IR.ExId "3.14159265458979323846"]
    , GStruct
        (IR.ExId "tf")
        [ (TInt, IR.ExId "a")
        , (TChar, IR.ExId "b")
        ]
    , GFuncDeclare Nothing TInt (IR.ExId "foo") [(TInt, IR.Empty)]
    , GFuncDef
        Nothing
        TInt
        (IR.ExId "main")
        [(TInt, IR.ExId "argc"), (TPointer (TPointer TChar), IR.ExId "argv")]
        ( SScope
            [ SVarDecl TInt (IR.ExId "test") Nothing
            , SVarDecl (TConstructor (TIdent $ IR.ExId "skepu::Vector") TInt) (IR.ExId "vec") $ Just [EInt 10]
            , SVarDecl (TConstructor (TIdent $ IR.ExId "skepu::Matrix") TInt) (IR.ExId "mat") $ Just [EInt 10, EInt 10]
            , SVarDef TAuto (IR.ExId "fwef") Nothing (ECall (IR.ExId "skepu::Map<2>") [])
            , SVarDef TAuto (IR.ExId "fwef") Nothing (ECall (IR.ExId "skepu::Reduce") [ELambda [] [(TInt, IR.ExId "a"), (TInt, IR.ExId "b")] (SScope [SReturn . Just $ EBinOp Add (EVar $ IR.ExId "a") (EVar $ IR.ExId "b")])])
            , SArrayDecl TChar (IR.ExId "s") [(EInt 2), (EInt 3)]
            , SVarAssign (IR.ExId "test") (EInt 1)
            , SVarAssign (IR.ExId "test") $ ECall (IR.ExId "foo") [EVar $ IR.ExId "test"]
            , SIf (EBinOp Less (EVar $ IR.ExId "test") (EInt 10)) (SExpr $ EUnOp PostIncrement $ EVar $ IR.ExId "test") (Just $ SExpr $ EUnOp PostDecrement $ EVar $ IR.ExId "test")
            , SIf (EBinOp Less (EVar $ IR.ExId "test") (EInt 10)) (SScope [SExpr $ EUnOp PostIncrement $ EVar $ IR.ExId "test"]) (Just $ SScope [SExpr $ EUnOp PostDecrement $ EVar $ IR.ExId "test"])
            , SExpr $
                ECall
                  (IR.ExId "skepu::external")
                  [ ELambda [IR.ExId "&"] [] $
                      SScope
                        []
                  ]
            , SStream (IR.ExId "std::cout") True [EString "Var a is: ", EVar (IR.ExId "a")]
            ]
        )
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
--     skepu::Vector<int> vec(10);
--     skepu::Matrix<int> mat(10, 10);
--     auto fwef = skepu::Map<2>();
--     auto fwef = skepu::Reduce([](int a, int b) {
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
--     skepu::external([&]() {
--
--     });
--     std::cout << "Var a is: " << a;
-- }

instance (Pretty a) => Pretty (Type a) where
  pretty = \case
    TVoid -> pretty "void"
    TInt -> pretty "int"
    TSizeT -> pretty "size_t"
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
        <+> braces
          ( line
              <> (indent 4 . vsep . map (<> semi) . map prettyParam) fields
              <> line
          )
        <> semi
    GMacro macro opt ->
      pretty "#" <> pretty macro <+> (hsep . map pretty) opt

prettyParam :: (Pretty a) => ((Type a), IR.Id a) -> Doc ann
prettyParam (t@(TPointer _), i) = pretty t <> pretty i
prettyParam (t, i) = pretty t <+> pretty i

instance (Pretty a) => Pretty (Program a) where
  pretty (Prog globals) =
    vsep . map pretty $ globals
