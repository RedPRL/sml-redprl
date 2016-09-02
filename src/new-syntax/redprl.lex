
type pos = Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref (Coord.init "-")
val eof = fn (fileName : string) => Tokens.EOF(!pos, !pos)

exception LexerError of pos

%%
%arg (fileName) :string;
%header (functor RedPrlLexFun (structure Tokens : RedPrl_TOKENS));
alpha = [A-Za-z];
digit = [0-9];
any = [@a-zA-Z0-9\'];
whitespace = [\ \t];
%%

\n                 => (pos := Coord.nextline (!pos); continue ());
{whitespace}+      => (pos := Coord.addchar (size yytext) (!pos); continue ());
{digit}+           => (Tokens.NUMERAL (valOf (Int.fromString yytext), !pos, !pos));


"("                => (Tokens.LPAREN (!pos, Coord.nextchar (!pos)));
")"                => (Tokens.RPAREN (!pos, Coord.nextchar (!pos)));
"{"                => (Tokens.LBRACKET (!pos, Coord.nextchar (!pos)));
"}"                => (Tokens.RBRACKET (!pos, Coord.nextchar (!pos)));
"["                => (Tokens.LSQUARE (!pos, Coord.nextchar (!pos)));
"]"                => (Tokens.RSQUARE (!pos, Coord.nextchar (!pos)));
"."                => (Tokens.DOT (!pos, Coord.nextchar (!pos)));
","                => (Tokens.COMMA (!pos, Coord.nextchar (!pos)));
":"                => (Tokens.COLON (!pos, Coord.nextchar (!pos)));
";"                => (Tokens.SEMI (!pos, Coord.nextchar (!pos)));
"#"                => (Tokens.HASH (!pos, Coord.nextchar (!pos)));
"="                => (Tokens.EQUALS (!pos, Coord.nextchar (!pos)));
"\'"               => (Tokens.APOSTROPHE (!pos, Coord.nextchar (!pos)));
"0"                => (Tokens.ZERO (!pos, Coord.nextchar (!pos)));
"1"                => (Tokens.ONE (!pos, Coord.nextchar (!pos)));
"~"                => (Tokens.SQUIGGLE (!pos, Coord.nextchar (!pos)));
"~>"               => (Tokens.SQUIGGLE_ARROW (!pos, Coord.addchar 2 (!pos)));
"->"               => (Tokens.RIGHT_ARROW (!pos, Coord.addchar 2 (!pos)));
"<-"               => (Tokens.LEFT_ARROW (!pos, Coord.addchar 2 (!pos)));

"lam"              => (Tokens.LAMBDA (!pos, Coord.addchar 3 (!pos)));
"hcom"             => (Tokens.HCOM (!pos, Coord.addchar 4 (!pos)));
"coe"              => (Tokens.COE (!pos, Coord.addchar 3 (!pos)));

"dim"              => (Tokens.DIM (!pos, Coord.addchar 3 (!pos)));
"exn"              => (Tokens.EXN (!pos, Coord.addchar 3 (!pos)));
"lbl"              => (Tokens.LBL (!pos, Coord.addchar 3 (!pos)));

"exp"              => (Tokens.EXP (!pos, Coord.addchar 3 (!pos)));
"lvl"              => (Tokens.LVL (!pos, Coord.addchar 3 (!pos)));

"Def"              => (Tokens.DCL_DEF (!pos, Coord.addchar 3 (!pos)));
"Tac"              => (Tokens.DCL_TAC (!pos, Coord.addchar 3 (!pos)));
"Thm"              => (Tokens.DCL_THM (!pos, Coord.addchar 3 (!pos)));
"by"               => (Tokens.BY (!pos, Coord.addchar 2 (!pos)));

"id"               => (Tokens.TAC_ID (!pos, Coord.addchar 2 (!pos)));

{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, Coord.addchar (size yytext) (!pos)));
