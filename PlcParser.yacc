%%

%name PlcParser

%pos int

%term VAR | END | FN | REC
    | IF | THEN | ELSE
    | MATCH | WITH
    | NOT | AND
    | HD | TL | ISE
    | PRINT
    | PLUS | MINUS | MULTI | DIV 
    | EQ | INEQ | LESS | LESSEQ 
    | DOUBCOLON | COLON | SEMICOL | COMMA | ARROW | PIPE | UNDERSCORE | DOUBARROW
    | NIL | BOOL | INT
    | TRUE | FALSE
    | LPARENT | RPARENT | RBRACE | LBRACE | RBRACKET | LBRACKET
    | NAME of string | CINT of int | FUN
    | EOF


%nonterm Prog of expr 
    | Decl of expr
    | Expr of expr
    | AtomExpr of expr
    | AppExpr of expr
    | Const of expr
    | Comps of expr list
    | MatchExpr of (expr option * expr) list 
    | CondExpr of expr option
    | Args of (plcType * string) list
    | Params of (plcType * string) list
    | TypedVar of plcType * string
    | Type of plcType
    | AtomType of plcType
    | Types of plcType list


%eop EOF

%right SEMICOL ARROW
%nonassoc IF
%left ELSE 
%left AND 
%left EQ INEQ
%left LESS LESSEQ
%right DOUBCOLON
%left PLUS MINUS
%left MULTI DIV
%nonassoc NOT HD TL ISE PRINT NAME
%left LBRACKET

%noshift EOF

%start Prog

%%

Prog: Expr (Expr) 
    | Decl (Decl)

Decl: VAR NAME EQ Expr SEMICOL Prog (Let(NAME, Expr, Prog))
    | FUN NAME Args EQ Expr SEMICOL Prog (Let(NAME, makeAnon(Args, Expr), Prog))
    | FUN REC NAME Args COLON Type EQ Expr SEMICOL Prog (makeFun(NAME, Args, Type, Expr, Prog))

Expr: AtomExpr(AtomExpr)
    | AppExpr(AppExpr)
    | IF Expr THEN Expr ELSE Expr (If(Expr1, Expr2, Expr3))
    | MATCH Expr WITH MatchExpr (Match (Expr, MatchExpr))
    | NOT Expr (Prim1("!", Expr))
    | Expr AND Expr (Prim2("&&", Expr1, Expr2))
    | HD Expr (Prim1("hd", Expr))
    | TL Expr (Prim1("tl", Expr))
    | ISE Expr (Prim1("ise", Expr))
    | PRINT Expr (Prim1("print", Expr))
    | Expr PLUS Expr (Prim2("+", Expr1, Expr2))
    | Expr MINUS Expr (Prim2("-", Expr1, Expr2))
    | Expr MULTI Expr (Prim2("*", Expr1, Expr2))
    | Expr DIV Expr (Prim2("/", Expr1, Expr2))
    | MINUS Expr (Prim1("-", Expr))
    | Expr EQ Expr (Prim2("=", Expr1, Expr2))
    | Expr INEQ Expr (Prim2("!=", Expr1, Expr2))
    | Expr LESS Expr (Prim2("<", Expr1, Expr2))
    | Expr LESSEQ Expr (Prim2("<=", Expr1, Expr2))
    | Expr DOUBCOLON Expr (Prim2("::", Expr1, Expr2))
    | Expr SEMICOL Expr (Prim2(";", Expr1, Expr2))
    | Expr LBRACKET CINT RBRACKET (Item (CINT, Expr))

AtomExpr: Const (Const)
    | NAME (Var(NAME))
    | LBRACE Prog RBRACE (Prog)
    | LPARENT Comps RPARENT (List Comps)
    | LPARENT Expr RPARENT (Expr)
    | FN Args DOUBARROW Expr END (makeAnon(Args, Expr))

AppExpr: AtomExpr AtomExpr (Call(AtomExpr1, AtomExpr2))
    | AppExpr AtomExpr (Call(AppExpr, AtomExpr))

Const: TRUE (ConB true) | FALSE (ConB false)
    | CINT (ConI CINT)
    | LPARENT RPARENT (List [])
    | LPARENT Type LBRACKET RBRACKET RPARENT (ESeq(Type))

Comps: Expr COMMA Expr (Expr1 :: Expr2 :: [])
    | Expr COMMA Comps (Expr :: Comps)

MatchExpr: END ([])
    | PIPE CondExpr ARROW Expr MatchExpr ((CondExpr, Expr) :: MatchExpr)

CondExpr: Expr (SOME(Expr))
    | UNDERSCORE (NONE)

Args: LPARENT RPARENT ([])
    | LPARENT Params RPARENT (Params)

Params : TypedVar (TypedVar::[])
    | TypedVar COMMA Params (TypedVar::Params)

TypedVar: Type NAME ((Type, NAME))

Type: AtomType(AtomType)
    | LPARENT Types RPARENT (ListT Types)
    | LBRACKET Type RBRACKET (SeqT Type)
    | Type ARROW Type (FunT (Type1, Type2))

AtomType: NIL (ListT [])
    | BOOL (BoolT)
    | INT (IntT)
    | LPARENT Type RPARENT (Type)

Types: Type COMMA Type (Type1 :: Type2 :: [])
    | Type COMMA Types (Type :: Types)