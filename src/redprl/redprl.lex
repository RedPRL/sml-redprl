
type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fileName : string) => Tokens.EOF (!pos, !pos)

local
  val commentLevel = ref 0
in
  fun commentPush () = 
    commentLevel := !commentLevel + 1

  fun commentPop () = 
    (commentLevel := !commentLevel - 1;
     !commentLevel = 0)
end

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
%s COMMENT;
upper = [A-Z];
lower = [a-z];
digit = [0-9];
identChr = [a-zA-Z0-9\'/-];
whitespace = [\ \t];
%%

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (incPos (size yytext); continue ());
<INITIAL>"-"?{digit}+       => (Tokens.NUMERAL (posTupleWith (size yytext) (valOf (IntInf.fromString yytext))));
<INITIAL>"//"[^\n]*         => (continue ());
"/*" => (commentPush (); YYBEGIN COMMENT; continue ());
"*/" => (if commentPop () then (YYBEGIN INITIAL; continue ()) else continue ());
<COMMENT>. => (continue ());

<INITIAL>":>"               => (Tokens.TRIANGLE_RIGHT (posTuple (size yytext)));
<INITIAL>"<|"               => (Tokens.LANGLE_PIPE (posTuple (size yytext)));
<INITIAL>"|>"               => (Tokens.RANGLE_PIPE (posTuple (size yytext)));
<INITIAL>"("                => (Tokens.LPAREN (posTuple (size yytext)));
<INITIAL>")"                => (Tokens.RPAREN (posTuple (size yytext)));
<INITIAL>"<"                => (Tokens.LANGLE (posTuple (size yytext)));
<INITIAL>">"                => (Tokens.RANGLE (posTuple (size yytext)));
<INITIAL>"{"                => (Tokens.LBRACKET (posTuple (size yytext)));
<INITIAL>"}"                => (Tokens.RBRACKET (posTuple (size yytext)));
<INITIAL>"["                => (Tokens.LSQUARE (posTuple (size yytext)));
<INITIAL>"]"                => (Tokens.RSQUARE (posTuple (size yytext)));
<INITIAL>"."                => (Tokens.DOT (posTuple (size yytext)));
<INITIAL>","                => (Tokens.COMMA (posTuple (size yytext)));
<INITIAL>"&"                => (Tokens.AMPERSAND (posTuple (size yytext)));
<INITIAL>":"                => (Tokens.COLON (posTuple (size yytext)));
<INITIAL>";"                => (Tokens.SEMI (posTuple (size yytext)));
<INITIAL>"#"                => (Tokens.HASH (posTuple (size yytext)));
<INITIAL>"="                => (Tokens.EQUALS (posTuple (size yytext)));
<INITIAL>"->"               => (Tokens.RIGHT_ARROW (posTuple (size yytext)));
<INITIAL>"<-"               => (Tokens.LEFT_ARROW (posTuple (size yytext)));
<INITIAL>"~>"               => (Tokens.SQUIGGLE_RIGHT_ARROW (posTuple (size yytext)));
<INITIAL>"<~"               => (Tokens.SQUIGGLE_LEFT_ARROW (posTuple (size yytext)));
<INITIAL>"=>"               => (Tokens.DOUBLE_RIGHT_ARROW (posTuple (size yytext)));
<INITIAL>"==>"              => (Tokens.LONG_RIGHT_ARROW (posTuple (size yytext)));
<INITIAL>"`"                => (Tokens.BACK_TICK (posTuple (size yytext)));
<INITIAL>"*"                => (Tokens.TIMES (posTuple (size yytext)));
<INITIAL>"!"                => (Tokens.BANG (posTuple (size yytext)));
<INITIAL>"@"                => (Tokens.AT_SIGN (posTuple (size yytext)));
<INITIAL>"$"                => (Tokens.DOLLAR_SIGN (posTuple (size yytext)));
<INITIAL>"||"               => (Tokens.DOUBLE_PIPE (posTuple (size yytext)));
<INITIAL>"|"                => (Tokens.PIPE (posTuple (size yytext)));
<INITIAL>"%"                => (Tokens.PERCENT (posTuple (size yytext)));
<INITIAL>"_"                => (Tokens.UNDER (posTuple (size yytext)));
<INITIAL>"+"                => (Tokens.PLUS (posTuple (size yytext)));
<INITIAL>"++"               => (Tokens.DOUBLE_PLUS (posTuple (size yytext)));


<INITIAL>"ax"               => (Tokens.AX (posTuple (size yytext)));
<INITIAL>"fcom"             => (Tokens.FCOM (posTuple (size yytext)));
<INITIAL>"bool"             => (Tokens.BOOL (posTuple (size yytext)));
<INITIAL>"tt"               => (Tokens.TT (posTuple (size yytext)));
<INITIAL>"ff"               => (Tokens.FF (posTuple (size yytext)));
<INITIAL>"if"               => (Tokens.IF (posTuple (size yytext)));
<INITIAL>"nat"              => (Tokens.NAT (posTuple (size yytext)));
<INITIAL>"zero"             => (Tokens.ZERO (posTuple (size yytext)));
<INITIAL>"succ"             => (Tokens.SUCC (posTuple (size yytext)));
<INITIAL>"nat-rec"          => (Tokens.NAT_REC (posTuple (size yytext)));
<INITIAL>"int"              => (Tokens.INT (posTuple (size yytext)));
<INITIAL>"negsucc"          => (Tokens.NEGSUCC (posTuple (size yytext)));
<INITIAL>"int-rec"          => (Tokens.INT_REC (posTuple (size yytext)));
<INITIAL>"void"             => (Tokens.VOID (posTuple (size yytext)));
<INITIAL>"S1"               => (Tokens.S1 (posTuple (size yytext)));
<INITIAL>"base"             => (Tokens.BASE (posTuple (size yytext)));
<INITIAL>"loop"             => (Tokens.LOOP (posTuple (size yytext)));
<INITIAL>"S1-rec"           => (Tokens.S1_REC (posTuple (size yytext)));
<INITIAL>"lam"              => (Tokens.LAMBDA (posTuple (size yytext)));
<INITIAL>"record"           => (Tokens.RECORD (posTuple (size yytext)));
<INITIAL>"tuple"            => (Tokens.TUPLE (posTuple (size yytext)));
<INITIAL>"path"             => (Tokens.PATH (posTuple (size yytext)));
<INITIAL>"line"             => (Tokens.LINE (posTuple (size yytext))); 
<INITIAL>"pushout"          => (Tokens.PUSHOUT (posTuple (size yytext)));
<INITIAL>"left"             => (Tokens.LEFT (posTuple (size yytext)));
<INITIAL>"right"            => (Tokens.RIGHT (posTuple (size yytext)));
<INITIAL>"glue"             => (Tokens.GLUE (posTuple (size yytext)));
<INITIAL>"pushout-rec"      => (Tokens.PUSHOUT_REC (posTuple (size yytext)));
<INITIAL>"coeq"             => (Tokens.COEQUALIZER (posTuple (size yytext)));
<INITIAL>"cecod"            => (Tokens.CECOD (posTuple (size yytext)));
<INITIAL>"cedom"            => (Tokens.CEDOM (posTuple (size yytext)));
<INITIAL>"coeq-rec"         => (Tokens.COEQUALIZER_REC (posTuple (size yytext)));
<INITIAL>"mem"              => (Tokens.MEM (posTuple (size yytext)));
<INITIAL>"ni"               => (Tokens.MEM (posTuple (size yytext)));
<INITIAL>"box"              => (Tokens.BOX (posTuple (size yytext)));
<INITIAL>"cap"              => (Tokens.CAP (posTuple (size yytext)));
<INITIAL>"V"                => (Tokens.V (posTuple (size yytext)));
<INITIAL>"VV"               => (Tokens.V (posTuple (size yytext)));
<INITIAL>"WU"               => (Tokens.V (posTuple (size yytext)));
<INITIAL>"Vin"              => (Tokens.VIN (posTuple (size yytext)));
<INITIAL>"Vproj"            => (Tokens.VPROJ (posTuple (size yytext)));
<INITIAL>"U"                => (Tokens.UNIVERSE (posTuple (size yytext)));
<INITIAL>"abs"              => (Tokens.ABS (posTuple (size yytext)));
<INITIAL>"hcom"             => (Tokens.HCOM (posTuple (size yytext)));
<INITIAL>"com"              => (Tokens.COM (posTuple (size yytext)));
<INITIAL>"coe"              => (Tokens.COE (posTuple (size yytext)));

<INITIAL>"then"             => (Tokens.THEN (posTuple (size yytext)));
<INITIAL>"else"             => (Tokens.ELSE (posTuple (size yytext)));
<INITIAL>"let"              => (Tokens.LET (posTuple (size yytext)));
<INITIAL>"claim"            => (Tokens.CLAIM (posTuple (size yytext)));
<INITIAL>"use"              => (Tokens.USE (posTuple (size yytext)));
<INITIAL>"with"             => (Tokens.WITH (posTuple (size yytext)));
<INITIAL>"without"          => (Tokens.WITHOUT (posTuple (size yytext)));
<INITIAL>"case"             => (Tokens.CASE (posTuple (size yytext)));
<INITIAL>"of"               => (Tokens.OF (posTuple (size yytext)));
<INITIAL>"refine"           => (Tokens.REFINE (posTuple (size yytext)));

<INITIAL>"dim"              => (Tokens.DIM (posTuple (size yytext)));
<INITIAL>"lvl"              => (Tokens.LVL (posTuple (size yytext)));
<INITIAL>"knd"              => (Tokens.KND (posTuple (size yytext)));

<INITIAL>"lmax"             => (Tokens.LMAX (posTuple (size yytext)));

<INITIAL>"exp"              => (Tokens.EXP (posTuple (size yytext)));
<INITIAL>"tac"              => (Tokens.TAC (posTuple (size yytext)));
<INITIAL>"jdg"              => (Tokens.JDG (posTuple (size yytext)));

<INITIAL>"Print"            => (Tokens.CMD_PRINT (posTuple (size yytext)));
<INITIAL>"Extract"          => (Tokens.CMD_EXTRACT (posTuple (size yytext)));
<INITIAL>"Quit"             => (Tokens.CMD_QUIT (posTuple (size yytext)));
<INITIAL>"Def"              => (Tokens.DCL_DEF (posTuple (size yytext)));
<INITIAL>"Tac"              => (Tokens.DCL_TAC (posTuple (size yytext)));
<INITIAL>"Thm"              => (Tokens.DCL_THM (posTuple (size yytext)));
<INITIAL>"by"               => (Tokens.BY (posTuple (size yytext)));
<INITIAL>"in"               => (Tokens.IN (posTuple (size yytext)));

<INITIAL>"repeat"           => (Tokens.MTAC_REPEAT (posTuple (size yytext)));
<INITIAL>"progress"         => (Tokens.MTAC_PROGRESS (posTuple (size yytext)));
<INITIAL>"id"               => (Tokens.TAC_ID (posTuple (size yytext)));
<INITIAL>"fail"             => (Tokens.TAC_FAIL (posTuple (size yytext)));
<INITIAL>"symmetry"         => (Tokens.TAC_SYMMETRY (posTuple (size yytext)));
<INITIAL>"auto-step"        => (Tokens.TAC_AUTO_STEP (posTuple (size yytext)));
<INITIAL>"auto"             => (Tokens.MTAC_AUTO (posTuple (size yytext)));
<INITIAL>"elim"             => (Tokens.TAC_ELIM (posTuple (size yytext)));
<INITIAL>"rewrite"          => (Tokens.TAC_REWRITE (posTuple (size yytext)));
<INITIAL>"reduce"           => (Tokens.TAC_REDUCE (posTuple (size yytext)));
<INITIAL>"unfold"           => (Tokens.TAC_UNFOLD (posTuple (size yytext)));
<INITIAL>"exact"            => (Tokens.RULE_EXACT (posTuple (size yytext)));
<INITIAL>"inversion"        => (Tokens.TAC_INVERSION (posTuple (size yytext)));
<INITIAL>"assumption"       => (Tokens.TAC_ASSUMPTION (posTuple (size yytext)));

<INITIAL>"match"            => (Tokens.MATCH (posTuple (size yytext)));
<INITIAL>"query"            => (Tokens.QUERY (posTuple (size yytext)));
<INITIAL>"concl"            => (Tokens.CONCL (posTuple (size yytext)));
<INITIAL>"print"            => (Tokens.PRINT (posTuple (size yytext)));

<INITIAL>"true"             => (Tokens.TRUE (posTuple (size yytext)));
<INITIAL>"type"             => (Tokens.TYPE (posTuple (size yytext)));
<INITIAL>"discrete"         => (Tokens.DISCRETE (posTuple (size yytext)));
<INITIAL>"kan"              => (Tokens.KAN (posTuple (size yytext)));
<INITIAL>"pre"              => (Tokens.PRE (posTuple (size yytext)));
<INITIAL>"at"               => (Tokens.AT (posTuple (size yytext)));

<INITIAL>{lower}{identChr}* => (Tokens.VARNAME (posTupleWith (size yytext) yytext));
<INITIAL>{upper}{identChr}* => (Tokens.OPNAME (posTupleWith (size yytext) yytext));
<INITIAL>"?"{identChr}*     => (Tokens.HOLENAME (posTupleWith (size yytext) yytext));

.                  => (RedPrlLog.print RedPrlLog.FAIL (SOME (Pos.pos (!pos yyarg) (!pos yyarg)), Fpp.text ("lexical error: skipping unrecognized character '" ^ yytext ^ "'")); continue ());
