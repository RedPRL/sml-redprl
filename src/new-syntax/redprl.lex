
type pos = Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token

val pos = ref (Coord.init "-")
val eof = fn () => Tokens.EOF(!pos, !pos)

exception LexerError of pos

%%
%arg (fileName) : string;
%header (functor RedPrlLexFun (structure Tokens : RedPrl_TOKENS));
alpha = [A-Za-z];
digit = [0-9];
any = [@a-zA-Z0-9];
whitespace = [\ \t];
%%

\n                 => (pos := Coord.nextline (!pos); lex ());
{whitespace}+      => (pos := Coord.addchar (size yytext) (!pos); lex ());

"("                => (Tokens.LPAREN (!pos, Coord.nextchar (!pos)));
")"                => (Tokens.RPAREN (!pos, Coord.nextchar (!pos)));
"{"                => (Tokens.RBRACKET (!pos, Coord.nextchar (!pos)));
"}"                => (Tokens.LBRACKET (!pos, Coord.nextchar (!pos)));
"["                => (Tokens.LSQUARE (!pos, Coord.nextchar (!pos)));
"]"                => (Tokens.RSQUARE (!pos, Coord.nextchar (!pos)));
"."                => (Tokens.DOT (!pos, Coord.nextchar (!pos)));
":"                => (Tokens.COLON (!pos, Coord.nextchar (!pos)));
";"                => (Tokens.SEMI (!pos, Coord.nextchar (!pos)));
"#"                => (Tokens.HASH (!pos, Coord.nextchar (!pos)));
"\'"               => (Tokens.APOSTROPHE (!pos, Coord.nextchar (!pos)));
"0"                => (Tokens.ZERO (!pos, Coord.nextchar (!pos)));
"1"                => (Tokens.ONE (!pos, Coord.nextchar (!pos)));

{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, Coord.addchar (size yytext) (!pos)));
