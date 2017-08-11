
functor ParseFn
   (structure Streamable : STREAMABLE
    structure Arg :
       sig
          type string
          type syn

          val fn_ : string * syn -> syn
          val app_exp : syn -> syn
          val app : syn * syn -> syn
          val atm_app : syn -> syn
          val let_ : string * syn * syn -> syn
          val pair : syn * syn -> syn
          val nil_ : unit -> syn
          val var : string -> syn

          datatype terminal =
             LET
           | FN
           | IN
           | DOUBLE_RIGHT_ARROW
           | LBRACKET
           | RBRACKET
           | LSQUARE
           | RSQUARE
           | LPAREN
           | RPAREN
           | DOT
           | COMMA
           | EQUALS
           | END
           | IDENT of string

          val error : terminal Streamable.t -> exn
       end)
   :>
   sig
      val parse : Arg.terminal Streamable.t -> Arg.syn * Arg.terminal Streamable.t
   end
=

(*

AUTOMATON LISTING
=================

State 0:

start -> . Exp  / 0
0 : Atm -> . IDENT  / 1
1 : Atm -> . LPAREN RPAREN  / 1
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 1
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 1
4 : App -> . Atm  / 1
5 : App -> . App Atm  / 1
6 : Exp -> . App  / 0
7 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 0

LET => shift 2
FN => shift 1
LPAREN => shift 3
IDENT => shift 6
Exp => goto 5
Atm => goto 7
App => goto 4

-----

State 1:

7 : Exp -> FN . IDENT DOUBLE_RIGHT_ARROW Exp  / 2

IDENT => shift 8

-----

State 2:

3 : Atm -> LET . IDENT EQUALS Exp IN Exp END  / 3

IDENT => shift 9

-----

State 3:

0 : Atm -> . IDENT  / 4
1 : Atm -> . LPAREN RPAREN  / 4
1 : Atm -> LPAREN . RPAREN  / 3
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
2 : Atm -> LPAREN . Exp COMMA Exp RPAREN  / 3
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 4
4 : App -> . Atm  / 4
5 : App -> . App Atm  / 4
6 : Exp -> . App  / 5
7 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 5

LET => shift 2
FN => shift 1
LPAREN => shift 3
RPAREN => shift 11
IDENT => shift 6
Exp => goto 10
Atm => goto 7
App => goto 4

-----

State 4:

0 : Atm -> . IDENT  / 3
1 : Atm -> . LPAREN RPAREN  / 3
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 3
5 : App -> App . Atm  / 3
6 : Exp -> App .  / 2

$ => reduce 6
LET => shift 2
IN => reduce 6
LPAREN => shift 3
RPAREN => reduce 6
COMMA => reduce 6
END => reduce 6
IDENT => shift 6
Atm => goto 12

-----

State 5:

start -> Exp .  / 0

$ => accept

-----

State 6:

0 : Atm -> IDENT .  / 3

$ => reduce 0
LET => reduce 0
IN => reduce 0
LPAREN => reduce 0
RPAREN => reduce 0
COMMA => reduce 0
END => reduce 0
IDENT => reduce 0

-----

State 7:

4 : App -> Atm .  / 3

$ => reduce 4
LET => reduce 4
IN => reduce 4
LPAREN => reduce 4
RPAREN => reduce 4
COMMA => reduce 4
END => reduce 4
IDENT => reduce 4

-----

State 8:

7 : Exp -> FN IDENT . DOUBLE_RIGHT_ARROW Exp  / 2

DOUBLE_RIGHT_ARROW => shift 13

-----

State 9:

3 : Atm -> LET IDENT . EQUALS Exp IN Exp END  / 3

EQUALS => shift 14

-----

State 10:

2 : Atm -> LPAREN Exp . COMMA Exp RPAREN  / 3

COMMA => shift 15

-----

State 11:

1 : Atm -> LPAREN RPAREN .  / 3

$ => reduce 1
LET => reduce 1
IN => reduce 1
LPAREN => reduce 1
RPAREN => reduce 1
COMMA => reduce 1
END => reduce 1
IDENT => reduce 1

-----

State 12:

5 : App -> App Atm .  / 3

$ => reduce 5
LET => reduce 5
IN => reduce 5
LPAREN => reduce 5
RPAREN => reduce 5
COMMA => reduce 5
END => reduce 5
IDENT => reduce 5

-----

State 13:

0 : Atm -> . IDENT  / 3
1 : Atm -> . LPAREN RPAREN  / 3
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 3
4 : App -> . Atm  / 3
5 : App -> . App Atm  / 3
6 : Exp -> . App  / 2
7 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 2
7 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW . Exp  / 2

LET => shift 2
FN => shift 1
LPAREN => shift 3
IDENT => shift 6
Exp => goto 16
Atm => goto 7
App => goto 4

-----

State 14:

0 : Atm -> . IDENT  / 6
1 : Atm -> . LPAREN RPAREN  / 6
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 6
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 6
3 : Atm -> LET IDENT EQUALS . Exp IN Exp END  / 3
4 : App -> . Atm  / 6
5 : App -> . App Atm  / 6
6 : Exp -> . App  / 7
7 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 7

LET => shift 2
FN => shift 1
LPAREN => shift 3
IDENT => shift 6
Exp => goto 17
Atm => goto 7
App => goto 4

-----

State 15:

0 : Atm -> . IDENT  / 8
1 : Atm -> . LPAREN RPAREN  / 8
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 8
2 : Atm -> LPAREN Exp COMMA . Exp RPAREN  / 3
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 8
4 : App -> . Atm  / 8
5 : App -> . App Atm  / 8
6 : Exp -> . App  / 9
7 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 9

LET => shift 2
FN => shift 1
LPAREN => shift 3
IDENT => shift 6
Exp => goto 18
Atm => goto 7
App => goto 4

-----

State 16:

7 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW Exp .  / 2

$ => reduce 7
IN => reduce 7
RPAREN => reduce 7
COMMA => reduce 7
END => reduce 7

-----

State 17:

3 : Atm -> LET IDENT EQUALS Exp . IN Exp END  / 3

IN => shift 19

-----

State 18:

2 : Atm -> LPAREN Exp COMMA Exp . RPAREN  / 3

RPAREN => shift 20

-----

State 19:

0 : Atm -> . IDENT  / 10
1 : Atm -> . LPAREN RPAREN  / 10
2 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 10
3 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 10
3 : Atm -> LET IDENT EQUALS Exp IN . Exp END  / 3
4 : App -> . Atm  / 10
5 : App -> . App Atm  / 10
6 : Exp -> . App  / 11
7 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 11

LET => shift 2
FN => shift 1
LPAREN => shift 3
IDENT => shift 6
Exp => goto 21
Atm => goto 7
App => goto 4

-----

State 20:

2 : Atm -> LPAREN Exp COMMA Exp RPAREN .  / 3

$ => reduce 2
LET => reduce 2
IN => reduce 2
LPAREN => reduce 2
RPAREN => reduce 2
COMMA => reduce 2
END => reduce 2
IDENT => reduce 2

-----

State 21:

3 : Atm -> LET IDENT EQUALS Exp IN Exp . END  / 3

END => shift 22

-----

State 22:

3 : Atm -> LET IDENT EQUALS Exp IN Exp END .  / 3

$ => reduce 3
LET => reduce 3
IN => reduce 3
LPAREN => reduce 3
RPAREN => reduce 3
COMMA => reduce 3
END => reduce 3
IDENT => reduce 3

-----

lookahead 0 = $ 
lookahead 1 = $ LET LPAREN IDENT 
lookahead 2 = $ IN RPAREN COMMA END 
lookahead 3 = $ LET IN LPAREN RPAREN COMMA END IDENT 
lookahead 4 = LET LPAREN COMMA IDENT 
lookahead 5 = COMMA 
lookahead 6 = LET IN LPAREN IDENT 
lookahead 7 = IN 
lookahead 8 = LET LPAREN RPAREN IDENT 
lookahead 9 = RPAREN 
lookahead 10 = LET LPAREN END IDENT 
lookahead 11 = END 

*)

struct
local
structure Value = struct
datatype nonterminal =
nonterminal
| string of Arg.string
| syn of Arg.syn
end
structure ParseEngine = ParseEngineFun (structure Streamable = Streamable
type terminal = Arg.terminal
type value = Value.nonterminal
val dummy = Value.nonterminal
fun read terminal =
(case terminal of
Arg.LET => (1, Value.nonterminal)
| Arg.FN => (2, Value.nonterminal)
| Arg.IN => (3, Value.nonterminal)
| Arg.DOUBLE_RIGHT_ARROW => (4, Value.nonterminal)
| Arg.LBRACKET => (5, Value.nonterminal)
| Arg.RBRACKET => (6, Value.nonterminal)
| Arg.LSQUARE => (7, Value.nonterminal)
| Arg.RSQUARE => (8, Value.nonterminal)
| Arg.LPAREN => (9, Value.nonterminal)
| Arg.RPAREN => (10, Value.nonterminal)
| Arg.DOT => (11, Value.nonterminal)
| Arg.COMMA => (12, Value.nonterminal)
| Arg.EQUALS => (13, Value.nonterminal)
| Arg.END => (14, Value.nonterminal)
| Arg.IDENT x => (15, Value.string x)
)
)
in
val parse = ParseEngine.parse (
ParseEngine.next5x1 "\128\131\130\128\128\128\128\128\128\132\128\128\128\128\128\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\137\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\138\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\132\140\128\128\128\128\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128x\131\128x\128\128\128\128\128\132x\128x\128x\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\127\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128~~\128~\128\128\128\128\128~~\128~\128~~\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128zz\128z\128\128\128\128\128zz\128z\128zz\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\142\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\144\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128}}\128}\128\128\128\128\128}}\128}\128}}\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128yy\128y\128\128\128\128\128yy\128y\128yy\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\132\128\128\128\128\128\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\132\128\128\128\128\128\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\132\128\128\128\128\128\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128w\128\128w\128\128\128\128\128\128w\128w\128w\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\132\128\128\128\128\128\135\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128||\128|\128\128\128\128\128||\128|\128||\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128{{\128{\128\128\128\128\128{{\128{\128{{\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
ParseEngine.next5x1 "\133\135\132\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\138\135\132\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\140\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\144\135\132\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\145\135\132\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\146\135\132\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\149\135\132\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
Vector.fromList [(1,1,(fn Value.string(arg0)::rest => Value.syn(Arg.var arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn _::_::rest => Value.syn(Arg.nil_ {})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn _::Value.syn(arg0)::_::Value.syn(arg1)::_::rest => Value.syn(Arg.pair {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,7,(fn _::Value.syn(arg0)::_::Value.syn(arg1)::_::Value.string(arg2)::_::rest => Value.syn(Arg.let_ {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(2,1,(fn Value.syn(arg0)::rest => Value.syn(Arg.atm_app arg0)::rest|_=>raise (Fail "bad parser"))),
(2,2,(fn Value.syn(arg0)::Value.syn(arg1)::rest => Value.syn(Arg.app {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(0,1,(fn Value.syn(arg0)::rest => Value.syn(Arg.app_exp arg0)::rest|_=>raise (Fail "bad parser"))),
(0,4,(fn Value.syn(arg0)::_::Value.string(arg1)::_::rest => Value.syn(Arg.fn_ {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser")))],
(fn Value.syn x => x | _ => raise (Fail "bad parser")), Arg.error)
end
end
