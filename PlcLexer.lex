(* Plc Lexer *)

(* User declarations *)

open Tokens
type pos = int
type slvalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (slvalue, pos) token

fun keyword (s, lpos, rpos) = 
	case s of 
    "var" => VAR(lpos, rpos)
    | "Bool" => BOOL(lpos, rpos)
    | "if" => IF(lpos, rpos)
    | "else" => ELSE(lpos, rpos)
    | "true" => TRUE(lpos, rpos)
    | "false" => FALSE(lpos, rpos)
    | "end" => END(lpos, rpos)
    | "then" => THEN(lpos, rpos)
    | "fn" => FN(lpos, rpos)
    | "fun" => FUN(lpos, rpos)
    | "hd" => HD(lpos, rpos)
    | "with" => WITH(lpos, rpos)
    | "Int" => INT(lpos, rpos)
    | "ise" => ISE(lpos, rpos)
    | "Nil" => NIL(lpos, rpos)
    | "match" => MATCH(lpos, rpos)
    | "rec" => REC(lpos, rpos)
    | "tl" => TL(lpos, rpos)
    | "print" => PRINT(lpos, rpos)
    | "_" => (UNDERSCORE(lpos, rpos))
    | _ => NAME(s,lpos, rpos)

(* A function to print a message error on the screen. *)
val error = fn x => TextIO.output(TextIO.stdOut, x ^ "\n")
val lineNumber = ref 0

(* Get the current line being read. *)
fun getLineAsString() =
    let
        val lineNum = !lineNumber
    in
        Int.toString lineNum
    end

fun strToInt s =
    case Int.fromString s of
    SOME i => i
    |  NONE => raise Fail ("Could not convert string '" ^ s ^ "' to integer")
    
(* Define what to do when the end of the file is reached. *)
fun eof () = Tokens.EOF(0,0)

(* Initialize the lexer. *)
fun init() = ()
%%

%header (functor PlcLexerFun(structure Tokens: PlcParser_TOKENS));

alpha=[A-Za-z];
digit=[0-9]*;
whitespace=[\ \t];
identifier=[a-zA-Z_][a-zA-Z_0-9]*;
%s COMMENTARY;

%%

\n => (lineNumber := !lineNumber + 1; lex());
{whitespace}+ => (lex());
{identifier} => (keyword(yytext, yypos, yypos));
{digit} => (CINT(strToInt(yytext), yypos, yypos));
"+" => (PLUS(yypos,yypos));
"-" => (MINUS(yypos,yypos));
"*" => (MULTI(yypos, yypos));
"/" => (DIV(yypos, yypos));
"(" => (LPARENT(yypos, yypos));
")" => (RPARENT(yypos, yypos));
"[" => (LBRACKET(yypos, yypos));
"]" => (RBRACKET(yypos, yypos));
"{" => (LBRACE(yypos, yypos));
"}" => (RBRACE(yypos, yypos));
"=" => (EQ(yypos, yypos));
"!=" => (INEQ(yypos, yypos));
"_" => (UNDERSCORE(yypos, yypos));
"&&" => (AND(yypos, yypos));
";" => (SEMICOL(yypos, yypos));
"!" => (NOT(yypos, yypos));
"," => (COMMA(yypos, yypos));
"|" => (PIPE(yypos, yypos));
"<" => (LESS(yypos, yypos));
"<=" => (LESSEQ(yypos, yypos));
"->" => (ARROW(yypos, yypos));
"=>" => (DOUBARROW(yypos, yypos));
":" => (COLON(yypos, yypos));
"::" => (DOUBCOLON(yypos, yypos));
. => (error("\n*** LEXER ERROR bad character ***\n"); 
raise Fail(" LEXER ERROR bad character "^yytext));

