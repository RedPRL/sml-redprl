
type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fileName : string) => Tokens.EOF (!pos, !pos)

fun incPos n = pos := (Coord.addchar n o (!pos))

fun posTuple n =
  let
    val l = !pos
    val () = incPos n
    val r = !pos
  in
    (l, r)
  end

fun posTupleWith n x =
  let
    val (l, r) = posTuple n
  in
    (x, l, r)
  end

%%
%arg (fileName : string);
%header (functor RedPrlLexFun (structure Tokens : RedPrl_TOKENS));
upper = [A-Z];
lower = [a-z];
digit = [0-9];
identChr = [a-zA-Z0-9\'/-];
whitespace = [\ \t];
%%

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (incPos (size yytext); continue ());
{digit}+           => (Tokens.NUMERAL (posTupleWith (size yytext) (valOf (Int.fromString yytext))));
"//"[^\n]*         => (continue ());


"<|"               => (Tokens.LANGLE_PIPE (posTuple (size yytext)));
"|>"               => (Tokens.RANGLE_PIPE (posTuple (size yytext)));
"("                => (Tokens.LPAREN (posTuple (size yytext)));
")"                => (Tokens.RPAREN (posTuple (size yytext)));
"<"                => (Tokens.LANGLE (posTuple (size yytext)));
">"                => (Tokens.RANGLE (posTuple (size yytext)));
"{"                => (Tokens.LBRACKET (posTuple (size yytext)));
"}"                => (Tokens.RBRACKET (posTuple (size yytext)));
"["                => (Tokens.LSQUARE (posTuple (size yytext)));
"]"                => (Tokens.RSQUARE (posTuple (size yytext)));
"."                => (Tokens.DOT (posTuple (size yytext)));
","                => (Tokens.COMMA (posTuple (size yytext)));
":"                => (Tokens.COLON (posTuple (size yytext)));
";"                => (Tokens.SEMI (posTuple (size yytext)));
"#"                => (Tokens.HASH (posTuple (size yytext)));
"="                => (Tokens.EQUALS (posTuple (size yytext)));
"\'"               => (Tokens.APOSTROPHE (posTuple (size yytext)));
"~"                => (Tokens.SQUIGGLE (posTuple (size yytext)));
"~>"               => (Tokens.SQUIGGLE_ARROW (posTuple (size yytext)));
"->"               => (Tokens.RIGHT_ARROW (posTuple (size yytext)));
"=>"               => (Tokens.DOUBLE_RIGHT_ARROW (posTuple (size yytext)));
"<-"               => (Tokens.LEFT_ARROW (posTuple (size yytext)));
"`"                => (Tokens.BACK_TICK (posTuple (size yytext)));
"*"                => (Tokens.TIMES (posTuple (size yytext)));
"@"                => (Tokens.AT_SIGN (posTuple (size yytext)));
"||"               => (Tokens.DOUBLE_PIPE (posTuple (size yytext)));
"|"                => (Tokens.PIPE (posTuple (size yytext)));
"%"                => (Tokens.PERCENT (posTuple (size yytext)));
"_"                => (Tokens.UNDER (posTuple (size yytext)));
">>"               => (Tokens.DOUBLE_RANGLE (posTuple (size yytext)));

"bool"             => (Tokens.BOOL (posTuple (size yytext)));
"sbool"            => (Tokens.S_BOOL (posTuple (size yytext)));
"tt"               => (Tokens.TT (posTuple (size yytext)));
"ff"               => (Tokens.FF (posTuple (size yytext)));
"if"               => (Tokens.IF (posTuple (size yytext)));
"if/s"             => (Tokens.S_IF (posTuple (size yytext)));
"paths"            => (Tokens.PATHS (posTuple (size yytext)));
"S1"               => (Tokens.S1 (posTuple (size yytext)));
"lam"              => (Tokens.LAMBDA (posTuple (size yytext)));
"hcom"             => (Tokens.HCOM (posTuple (size yytext)));
"coe"              => (Tokens.COE (posTuple (size yytext)));
"univ"             => (Tokens.UNIV (posTuple (size yytext)));
"loop"             => (Tokens.LOOP (posTuple (size yytext)));
"base"             => (Tokens.BASE (posTuple (size yytext)));
"fst"              => (Tokens.FST (posTuple (size yytext)));
"snd"              => (Tokens.SND (posTuple (size yytext)));

"then"             => (Tokens.THEN (posTuple (size yytext)));
"else"             => (Tokens.ELSE (posTuple (size yytext)));
"let"              => (Tokens.LET (posTuple (size yytext)));
"with"             => (Tokens.WITH (posTuple (size yytext)));
"case"             => (Tokens.CASE (posTuple (size yytext)));
"of"               => (Tokens.OF (posTuple (size yytext)));

"dim"              => (Tokens.DIM (posTuple (size yytext)));
"exn"              => (Tokens.EXN (posTuple (size yytext)));
"lbl"              => (Tokens.LBL (posTuple (size yytext)));

"exp"              => (Tokens.EXP (posTuple (size yytext)));
"tac"              => (Tokens.TAC (posTuple (size yytext)));
"lvl"              => (Tokens.LVL (posTuple (size yytext)));

"Print"            => (Tokens.CMD_PRINT (posTuple (size yytext)));
"Def"              => (Tokens.DCL_DEF (posTuple (size yytext)));
"Tac"              => (Tokens.DCL_TAC (posTuple (size yytext)));
"Thm"              => (Tokens.DCL_THM (posTuple (size yytext)));
"Rule"             => (Tokens.DCL_RULE (posTuple (size yytext)));
"by"               => (Tokens.BY (posTuple (size yytext)));
"in"               => (Tokens.IN (posTuple (size yytext)));

"rec"              => (Tokens.MTAC_REC (posTuple (size yytext)));
"repeat"           => (Tokens.MTAC_REPEAT (posTuple (size yytext)));
"progress"         => (Tokens.MTAC_PROGRESS (posTuple (size yytext)));
"id"               => (Tokens.RULE_ID (posTuple (size yytext)));
"eval-goal"        => (Tokens.RULE_EVAL_GOAL (posTuple (size yytext)));
"ceq/refl"         => (Tokens.RULE_CEQUIV_REFL (posTuple (size yytext)));
"symmetry"         => (Tokens.RULE_SYMMETRY (posTuple (size yytext)));
"auto-step"        => (Tokens.RULE_AUTO_STEP (posTuple (size yytext)));
"auto"             => (Tokens.MTAC_AUTO (posTuple (size yytext)));
"hyp"              => (Tokens.RULE_HYP (posTuple (size yytext)));
"elim"             => (Tokens.RULE_ELIM (posTuple (size yytext)));
"head-expand"      => (Tokens.RULE_HEAD_EXP (posTuple (size yytext)));
"lemma"            => (Tokens.RULE_LEMMA (posTuple (size yytext)));

"true"             => (Tokens.JDG_TRUE (posTuple (size yytext)));
"type"             => (Tokens.JDG_TYPE (posTuple (size yytext)));
"synth"            => (Tokens.JDG_SYNTH (posTuple (size yytext)));

{lower}{identChr}* => (Tokens.VARNAME (posTupleWith (size yytext) yytext));
{upper}{identChr}* => (Tokens.OPNAME (posTupleWith (size yytext) yytext));

.                  => (RedPrlLog.print RedPrlLog.FAIL (SOME (Pos.pos (!pos yyarg) (!pos yyarg)), "lexical error: skipping unrecognized character '" ^ yytext ^ "'"); continue ());
