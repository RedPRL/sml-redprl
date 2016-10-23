
type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fileName : string) => Tokens.EOF (!pos, !pos)

exception LexerError of pos

%%
%arg (fileName : string);
%header (functor RedPrlLexFun (structure Tokens : RedPrl_TOKENS));
alpha = [A-Za-z];
digit = [0-9];
any = [@a-zA-Z0-9\'];
whitespace = [\ \t];
%%

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (pos := (Coord.addchar (size yytext) o (!pos)); continue ());
{digit}+           => (Tokens.NUMERAL (valOf (Int.fromString yytext), !pos, Coord.addchar (size yytext) o (!pos)));
"//"[^\n]*         => (continue ());


"("                => (Tokens.LPAREN (!pos, Coord.nextchar o (!pos)));
")"                => (Tokens.RPAREN (!pos, Coord.nextchar o (!pos)));
"<"                => (Tokens.LANGLE (!pos, Coord.nextchar o (!pos)));
">"                => (Tokens.RANGLE (!pos, Coord.nextchar o (!pos)));
"{"                => (Tokens.LBRACKET (!pos, Coord.nextchar o (!pos)));
"}"                => (Tokens.RBRACKET (!pos, Coord.nextchar o (!pos)));
"["                => (Tokens.LSQUARE (!pos, Coord.nextchar o (!pos)));
"]"                => (Tokens.RSQUARE (!pos, Coord.nextchar o (!pos)));
"."                => (Tokens.DOT (!pos, Coord.nextchar o (!pos)));
","                => (Tokens.COMMA (!pos, Coord.nextchar o (!pos)));
":"                => (Tokens.COLON (!pos, Coord.nextchar o (!pos)));
";"                => (Tokens.SEMI (!pos, Coord.nextchar o (!pos)));
"#"                => (Tokens.HASH (!pos, Coord.nextchar o (!pos)));
"="                => (Tokens.EQUALS (!pos, Coord.nextchar o (!pos)));
"\'"               => (Tokens.APOSTROPHE (!pos, Coord.nextchar o (!pos)));
"~"                => (Tokens.SQUIGGLE (!pos, Coord.nextchar o (!pos)));
"~>"               => (Tokens.SQUIGGLE_ARROW (!pos, Coord.addchar 2 o (!pos)));
"->"               => (Tokens.RIGHT_ARROW (!pos, Coord.addchar 2 o (!pos)));
"=>"               => (Tokens.DOUBLE_RIGHT_ARROW (!pos, Coord.addchar 2 o (!pos)));
"<-"               => (Tokens.LEFT_ARROW (!pos, Coord.addchar 2 o (!pos)));
"`"                => (Tokens.BACK_TICK (!pos, Coord.nextchar o (!pos)));
"*"                => (Tokens.TIMES (!pos, Coord.nextchar o (!pos)));
"@"                => (Tokens.AT_SIGN (!pos, Coord.nextchar o (!pos)));
"||"               => (Tokens.DOUBLE_PIPE (!pos, Coord.addchar 2 o (!pos)));
"|"                => (Tokens.PIPE (!pos, Coord.nextchar o (!pos)));
"%"                => (Tokens.PERCENT (!pos, Coord.nextchar o (!pos)));

"bool"             => (Tokens.BOOL (!pos, Coord.addchar (size yytext) o (!pos)));
"sbool"            => (Tokens.S_BOOL (!pos, Coord.addchar (size yytext) o (!pos)));
"tt"               => (Tokens.TT (!pos, Coord.addchar (size yytext) o (!pos)));
"ff"               => (Tokens.FF (!pos, Coord.addchar (size yytext) o (!pos)));
"if"               => (Tokens.IF (!pos, Coord.addchar (size yytext) o (!pos)));
"if/s"             => (Tokens.S_IF (!pos, Coord.addchar (size yytext) o (!pos)));
"paths"            => (Tokens.PATHS (!pos, Coord.addchar (size yytext) o (!pos)));
"S1"               => (Tokens.S1 (!pos, Coord.addchar (size yytext) o (!pos)));
"lam"              => (Tokens.LAMBDA (!pos, Coord.addchar 3 o (!pos)));
"hcom"             => (Tokens.HCOM (!pos, Coord.addchar 4 o (!pos)));
"coe"              => (Tokens.COE (!pos, Coord.addchar 3 o (!pos)));
"univ"             => (Tokens.UNIV (!pos, Coord.addchar 4 o (!pos)));
"loop"             => (Tokens.LOOP (!pos, Coord.addchar (size yytext) o (!pos)));
"base"             => (Tokens.BASE (!pos, Coord.addchar (size yytext) o (!pos)));
"fst"              => (Tokens.FST (!pos, Coord.addchar (size yytext) o (!pos)));
"snd"              => (Tokens.SND (!pos, Coord.addchar (size yytext) o (!pos)));

"then"             => (Tokens.THEN (!pos, Coord.addchar (size yytext) o (!pos)));
"else"             => (Tokens.ELSE (!pos, Coord.addchar (size yytext) o (!pos)));
"let"              => (Tokens.LET (!pos, Coord.addchar (size yytext) o (!pos)));
"with"             => (Tokens.WITH (!pos, Coord.addchar (size yytext) o (!pos)));
"case"             => (Tokens.CASE (!pos, Coord.addchar (size yytext) o (!pos)));
"of"               => (Tokens.OF (!pos, Coord.addchar (size yytext) o (!pos)));

"dim"              => (Tokens.DIM (!pos, Coord.addchar 3 o (!pos)));
"exn"              => (Tokens.EXN (!pos, Coord.addchar 3 o (!pos)));
"lbl"              => (Tokens.LBL (!pos, Coord.addchar 3 o (!pos)));

"exp"              => (Tokens.EXP (!pos, Coord.addchar 3 o (!pos)));
"tac"              => (Tokens.TAC (!pos, Coord.addchar 3 o (!pos)));
"lvl"              => (Tokens.LVL (!pos, Coord.addchar 3 o (!pos)));

"Print"            => (Tokens.CMD_PRINT (!pos, Coord.addchar (size yytext) o (!pos)));
"Def"              => (Tokens.DCL_DEF (!pos, Coord.addchar 3 o (!pos)));
"Tac"              => (Tokens.DCL_TAC (!pos, Coord.addchar 3 o (!pos)));
"Thm"              => (Tokens.DCL_THM (!pos, Coord.addchar 3 o (!pos)));
"by"               => (Tokens.BY (!pos, Coord.addchar 2 o (!pos)));
"in"               => (Tokens.IN (!pos, Coord.addchar 2 o (!pos)));

"rec"              => (Tokens.TAC_REC (!pos, Coord.addchar (size yytext) o (!pos)));
"repeat"           => (Tokens.MTAC_REPEAT (!pos, Coord.addchar (size yytext) o (!pos)));
"progress"         => (Tokens.TAC_PROGRESS (!pos, Coord.addchar (size yytext) o (!pos)));
"id"               => (Tokens.RULE_ID (!pos, Coord.addchar 2 o (!pos)));
"eval-goal"        => (Tokens.RULE_EVAL_GOAL (!pos, Coord.addchar (size yytext) o (!pos)));
"ceq/refl"         => (Tokens.RULE_CEQUIV_REFL (!pos, Coord.addchar (size yytext) o (!pos)));
"symmetry"         => (Tokens.RULE_SYMMETRY (!pos, Coord.addchar (size yytext) o (!pos)));
"auto-step"        => (Tokens.RULE_AUTO_STEP (!pos, Coord.addchar (size yytext) o (!pos)));
"auto"             => (Tokens.MTAC_AUTO (!pos, Coord.addchar (size yytext) o (!pos)));
"hyp"              => (Tokens.RULE_HYP (!pos, Coord.addchar (size yytext) o (!pos)));
"elim"             => (Tokens.RULE_ELIM (!pos, Coord.addchar (size yytext) o (!pos)));
"head-expand"      => (Tokens.RULE_HEAD_EXP (!pos, Coord.addchar (size yytext) o (!pos)));
"lemma"            => (Tokens.RULE_LEMMA (!pos, Coord.addchar (size yytext) o (!pos)));

"true"             => (Tokens.JDG_TRUE (!pos, Coord.addchar 4 o (!pos)));
"type"             => (Tokens.JDG_TYPE (!pos, Coord.addchar 4 o (!pos)));
"synth"            => (Tokens.JDG_SYNTH (!pos, Coord.addchar 5 o (!pos)));

{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, Coord.addchar (size yytext) o (!pos)));
