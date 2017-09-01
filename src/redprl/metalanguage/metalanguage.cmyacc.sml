
functor MetalanguageParseFn
   (structure Streamable : STREAMABLE
    structure Arg :
       sig
          type pos
          type pos_string
          type exp
          type decl
          type decls
          type exps
          type names
          type oexp
          type oexps

          val oexpsNil : unit -> oexps
          val oexpsCons : oexp * oexps -> oexps
          val obinding : pos * names * pos -> oexp
          val ogroup : pos * oexps * pos -> oexp
          val oident : pos_string -> oexp
          val namesNil : unit -> names
          val namesSingl : pos_string -> names
          val namesCons : pos_string * names -> names
          val expsNil : unit -> exps
          val expsSingl : exp -> exps
          val expsCons : exp * exps -> exps
          val fn_ : pos * pos_string * exp -> exp
          val seqExpSnocFork : exp * exps * pos -> exp
          val seqExpSnoc : exp * exp -> exp
          val app : exp * exp -> exp
          val declsNil : unit -> decls
          val declsCons : decl * decls -> decls
          val declVal : pos_string * exp -> decl
          val print : pos * exp -> exp
          val push : pos * names * exp * pos -> exp
          val exact : pos * exp -> exp
          val refine : pos * pos_string -> exp
          val quote : pos * oexp -> exp
          val identity : exp -> exp
          val prove : pos * exp * exp * pos -> exp
          val let_ : pos * decls * exp * pos -> exp
          val proj2 : pos -> exp
          val proj1 : pos -> exp
          val pair : pos * exp * exp * pos -> exp
          val nil_ : pos * pos -> exp
          val goal : pos -> exp
          val var : pos_string -> exp

          datatype terminal =
             LET of pos
           | FN of pos
           | VAL of pos
           | IN of pos
           | BY of pos
           | DOUBLE_RIGHT_ARROW of pos
           | LSQUARE of pos
           | RSQUARE of pos
           | LPAREN of pos
           | RPAREN of pos
           | COMMA of pos
           | SEMI of pos
           | EQUALS of pos
           | BEGIN of pos
           | END of pos
           | IDENT of pos_string
           | PROVE of pos
           | PROJ1 of pos
           | PROJ2 of pos
           | BACKTICK of pos
           | REFINE of pos
           | GOAL of pos
           | PUSH of pos
           | PRINT of pos
           | EXACT of pos

          val error : terminal Streamable.t -> exn
       end)
   :>
   sig
      val parse : Arg.terminal Streamable.t -> Arg.exp * Arg.terminal Streamable.t
   end
=

(*

AUTOMATON LISTING
=================

State 0:

start -> . Exp  / 0
0 : Atm -> . IDENT  / 1
1 : Atm -> . GOAL  / 1
2 : Atm -> . LPAREN RPAREN  / 1
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 1
4 : Atm -> . PROJ1  / 1
5 : Atm -> . PROJ2  / 1
6 : Atm -> . LET Decls IN Exp END  / 1
7 : Atm -> . PROVE Exp BY Exp END  / 1
8 : Atm -> . LPAREN Exp RPAREN  / 1
9 : Atm -> . BEGIN Exp END  / 1
10 : Atm -> . BACKTICK OExp  / 1
11 : Atm -> . REFINE IDENT  / 1
12 : Atm -> . EXACT Atm  / 1
13 : Atm -> . PUSH Names IN Exp END  / 1
14 : Atm -> . PRINT Atm  / 1
18 : App -> . Atm  / 1
19 : App -> . App Atm  / 1
20 : SeqExp -> . App  / 2
21 : SeqExp -> . SeqExp SEMI App  / 2
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 2
23 : Exp -> . SeqExp  / 0
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 0

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 4
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 1:

24 : Exp -> FN . IDENT DOUBLE_RIGHT_ARROW Exp  / 3

IDENT => shift 19

-----

State 2:

6 : Atm -> LET . Decls IN Exp END  / 4
15 : Decl -> . VAL IDENT EQUALS Exp  / 5
16 : Decls -> . Decl Decls  / 6
17 : Decls -> .  / 6

VAL => shift 22
IN => reduce 17
Decls => goto 21
Decl => goto 20

-----

State 3:

0 : Atm -> . IDENT  / 4
1 : Atm -> . GOAL  / 4
2 : Atm -> . LPAREN RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 4
5 : Atm -> . PROJ2  / 4
6 : Atm -> . LET Decls IN Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 4
11 : Atm -> . REFINE IDENT  / 4
12 : Atm -> . EXACT Atm  / 4
13 : Atm -> . PUSH Names IN Exp END  / 4
14 : Atm -> . PRINT Atm  / 4
19 : App -> App . Atm  / 4
20 : SeqExp -> App .  / 7

$ => reduce 20
LET => shift 2
VAL => reduce 20
IN => reduce 20
BY => reduce 20
RSQUARE => reduce 20
LPAREN => shift 8
RPAREN => reduce 20
COMMA => reduce 20
SEMI => reduce 20
BEGIN => shift 9
END => reduce 20
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Atm => goto 23

-----

State 4:

start -> Exp .  / 0

$ => accept

-----

State 5:

0 : Atm -> . IDENT  / 4
1 : Atm -> . GOAL  / 4
2 : Atm -> . LPAREN RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 4
5 : Atm -> . PROJ2  / 4
6 : Atm -> . LET Decls IN Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 4
11 : Atm -> . REFINE IDENT  / 4
12 : Atm -> . EXACT Atm  / 4
13 : Atm -> . PUSH Names IN Exp END  / 4
14 : Atm -> . PRINT Atm  / 4
14 : Atm -> PRINT . Atm  / 4

LET => shift 2
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Atm => goto 24

-----

State 6:

1 : Atm -> GOAL .  / 4

$ => reduce 1
LET => reduce 1
VAL => reduce 1
IN => reduce 1
BY => reduce 1
RSQUARE => reduce 1
LPAREN => reduce 1
RPAREN => reduce 1
COMMA => reduce 1
SEMI => reduce 1
BEGIN => reduce 1
END => reduce 1
IDENT => reduce 1
PROVE => reduce 1
PROJ1 => reduce 1
PROJ2 => reduce 1
BACKTICK => reduce 1
REFINE => reduce 1
GOAL => reduce 1
PUSH => reduce 1
PRINT => reduce 1
EXACT => reduce 1

-----

State 7:

10 : Atm -> BACKTICK . OExp  / 4
31 : OExp -> . IDENT  / 4
32 : OExp -> . LPAREN OExps RPAREN  / 4
33 : OExp -> . LSQUARE OIdents RSQUARE  / 4

LSQUARE => shift 25
LPAREN => shift 26
IDENT => shift 27
OExp => goto 28

-----

State 8:

0 : Atm -> . IDENT  / 8
1 : Atm -> . GOAL  / 8
2 : Atm -> . LPAREN RPAREN  / 8
2 : Atm -> LPAREN . RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 8
3 : Atm -> LPAREN . Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 8
5 : Atm -> . PROJ2  / 8
6 : Atm -> . LET Decls IN Exp END  / 8
7 : Atm -> . PROVE Exp BY Exp END  / 8
8 : Atm -> . LPAREN Exp RPAREN  / 8
8 : Atm -> LPAREN . Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 8
10 : Atm -> . BACKTICK OExp  / 8
11 : Atm -> . REFINE IDENT  / 8
12 : Atm -> . EXACT Atm  / 8
13 : Atm -> . PUSH Names IN Exp END  / 8
14 : Atm -> . PRINT Atm  / 8
18 : App -> . Atm  / 8
19 : App -> . App Atm  / 8
20 : SeqExp -> . App  / 9
21 : SeqExp -> . SeqExp SEMI App  / 9
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 9
23 : Exp -> . SeqExp  / 10
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 10

LET => shift 2
FN => shift 1
LPAREN => shift 8
RPAREN => shift 30
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 29
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 9:

0 : Atm -> . IDENT  / 11
1 : Atm -> . GOAL  / 11
2 : Atm -> . LPAREN RPAREN  / 11
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 11
4 : Atm -> . PROJ1  / 11
5 : Atm -> . PROJ2  / 11
6 : Atm -> . LET Decls IN Exp END  / 11
7 : Atm -> . PROVE Exp BY Exp END  / 11
8 : Atm -> . LPAREN Exp RPAREN  / 11
9 : Atm -> . BEGIN Exp END  / 11
9 : Atm -> BEGIN . Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . PUSH Names IN Exp END  / 11
14 : Atm -> . PRINT Atm  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : SeqExp -> . App  / 12
21 : SeqExp -> . SeqExp SEMI App  / 12
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 12
23 : Exp -> . SeqExp  / 13
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 13

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 31
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 10:

0 : Atm -> . IDENT  / 14
1 : Atm -> . GOAL  / 14
2 : Atm -> . LPAREN RPAREN  / 14
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 14
4 : Atm -> . PROJ1  / 14
5 : Atm -> . PROJ2  / 14
6 : Atm -> . LET Decls IN Exp END  / 14
7 : Atm -> . PROVE Exp BY Exp END  / 14
7 : Atm -> PROVE . Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 14
9 : Atm -> . BEGIN Exp END  / 14
10 : Atm -> . BACKTICK OExp  / 14
11 : Atm -> . REFINE IDENT  / 14
12 : Atm -> . EXACT Atm  / 14
13 : Atm -> . PUSH Names IN Exp END  / 14
14 : Atm -> . PRINT Atm  / 14
18 : App -> . Atm  / 14
19 : App -> . App Atm  / 14
20 : SeqExp -> . App  / 15
21 : SeqExp -> . SeqExp SEMI App  / 15
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 15
23 : Exp -> . SeqExp  / 16
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 16

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 32
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 11:

0 : Atm -> IDENT .  / 4

$ => reduce 0
LET => reduce 0
VAL => reduce 0
IN => reduce 0
BY => reduce 0
RSQUARE => reduce 0
LPAREN => reduce 0
RPAREN => reduce 0
COMMA => reduce 0
SEMI => reduce 0
BEGIN => reduce 0
END => reduce 0
IDENT => reduce 0
PROVE => reduce 0
PROJ1 => reduce 0
PROJ2 => reduce 0
BACKTICK => reduce 0
REFINE => reduce 0
GOAL => reduce 0
PUSH => reduce 0
PRINT => reduce 0
EXACT => reduce 0

-----

State 12:

5 : Atm -> PROJ2 .  / 4

$ => reduce 5
LET => reduce 5
VAL => reduce 5
IN => reduce 5
BY => reduce 5
RSQUARE => reduce 5
LPAREN => reduce 5
RPAREN => reduce 5
COMMA => reduce 5
SEMI => reduce 5
BEGIN => reduce 5
END => reduce 5
IDENT => reduce 5
PROVE => reduce 5
PROJ1 => reduce 5
PROJ2 => reduce 5
BACKTICK => reduce 5
REFINE => reduce 5
GOAL => reduce 5
PUSH => reduce 5
PRINT => reduce 5
EXACT => reduce 5

-----

State 13:

4 : Atm -> PROJ1 .  / 4

$ => reduce 4
LET => reduce 4
VAL => reduce 4
IN => reduce 4
BY => reduce 4
RSQUARE => reduce 4
LPAREN => reduce 4
RPAREN => reduce 4
COMMA => reduce 4
SEMI => reduce 4
BEGIN => reduce 4
END => reduce 4
IDENT => reduce 4
PROVE => reduce 4
PROJ1 => reduce 4
PROJ2 => reduce 4
BACKTICK => reduce 4
REFINE => reduce 4
GOAL => reduce 4
PUSH => reduce 4
PRINT => reduce 4
EXACT => reduce 4

-----

State 14:

11 : Atm -> REFINE . IDENT  / 4

IDENT => shift 33

-----

State 15:

13 : Atm -> PUSH . Names IN Exp END  / 4
28 : Names -> . IDENT COMMA Names  / 6
29 : Names -> . IDENT  / 6
30 : Names -> .  / 6

IN => reduce 30
IDENT => shift 34
Names => goto 35

-----

State 16:

0 : Atm -> . IDENT  / 4
1 : Atm -> . GOAL  / 4
2 : Atm -> . LPAREN RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 4
5 : Atm -> . PROJ2  / 4
6 : Atm -> . LET Decls IN Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 4
11 : Atm -> . REFINE IDENT  / 4
12 : Atm -> . EXACT Atm  / 4
12 : Atm -> EXACT . Atm  / 4
13 : Atm -> . PUSH Names IN Exp END  / 4
14 : Atm -> . PRINT Atm  / 4

LET => shift 2
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Atm => goto 36

-----

State 17:

18 : App -> Atm .  / 4

$ => reduce 18
LET => reduce 18
VAL => reduce 18
IN => reduce 18
BY => reduce 18
RSQUARE => reduce 18
LPAREN => reduce 18
RPAREN => reduce 18
COMMA => reduce 18
SEMI => reduce 18
BEGIN => reduce 18
END => reduce 18
IDENT => reduce 18
PROVE => reduce 18
PROJ1 => reduce 18
PROJ2 => reduce 18
BACKTICK => reduce 18
REFINE => reduce 18
GOAL => reduce 18
PUSH => reduce 18
PRINT => reduce 18
EXACT => reduce 18

-----

State 18:

21 : SeqExp -> SeqExp . SEMI App  / 7
22 : SeqExp -> SeqExp . SEMI LSQUARE Exps RSQUARE  / 7
23 : Exp -> SeqExp .  / 3

$ => reduce 23
VAL => reduce 23
IN => reduce 23
BY => reduce 23
RSQUARE => reduce 23
RPAREN => reduce 23
COMMA => reduce 23
SEMI => shift 37
END => reduce 23

-----

State 19:

24 : Exp -> FN IDENT . DOUBLE_RIGHT_ARROW Exp  / 3

DOUBLE_RIGHT_ARROW => shift 38

-----

State 20:

15 : Decl -> . VAL IDENT EQUALS Exp  / 5
16 : Decls -> . Decl Decls  / 6
16 : Decls -> Decl . Decls  / 6
17 : Decls -> .  / 6

VAL => shift 22
IN => reduce 17
Decls => goto 39
Decl => goto 20

-----

State 21:

6 : Atm -> LET Decls . IN Exp END  / 4

IN => shift 40

-----

State 22:

15 : Decl -> VAL . IDENT EQUALS Exp  / 5

IDENT => shift 41

-----

State 23:

19 : App -> App Atm .  / 4

$ => reduce 19
LET => reduce 19
VAL => reduce 19
IN => reduce 19
BY => reduce 19
RSQUARE => reduce 19
LPAREN => reduce 19
RPAREN => reduce 19
COMMA => reduce 19
SEMI => reduce 19
BEGIN => reduce 19
END => reduce 19
IDENT => reduce 19
PROVE => reduce 19
PROJ1 => reduce 19
PROJ2 => reduce 19
BACKTICK => reduce 19
REFINE => reduce 19
GOAL => reduce 19
PUSH => reduce 19
PRINT => reduce 19
EXACT => reduce 19

-----

State 24:

14 : Atm -> PRINT Atm .  / 4

$ => reduce 14
LET => reduce 14
VAL => reduce 14
IN => reduce 14
BY => reduce 14
RSQUARE => reduce 14
LPAREN => reduce 14
RPAREN => reduce 14
COMMA => reduce 14
SEMI => reduce 14
BEGIN => reduce 14
END => reduce 14
IDENT => reduce 14
PROVE => reduce 14
PROJ1 => reduce 14
PROJ2 => reduce 14
BACKTICK => reduce 14
REFINE => reduce 14
GOAL => reduce 14
PUSH => reduce 14
PRINT => reduce 14
EXACT => reduce 14

-----

State 25:

33 : OExp -> LSQUARE . OIdents RSQUARE  / 17
36 : OIdents -> . IDENT OIdents  / 18
37 : OIdents -> .  / 18

RSQUARE => reduce 37
IDENT => shift 42
OIdents => goto 43

-----

State 26:

31 : OExp -> . IDENT  / 19
32 : OExp -> . LPAREN OExps RPAREN  / 19
32 : OExp -> LPAREN . OExps RPAREN  / 17
33 : OExp -> . LSQUARE OIdents RSQUARE  / 19
34 : OExps -> . OExp OExps  / 20
35 : OExps -> .  / 20

LSQUARE => shift 25
LPAREN => shift 26
RPAREN => reduce 35
IDENT => shift 27
OExp => goto 44
OExps => goto 45

-----

State 27:

31 : OExp -> IDENT .  / 17

$ => reduce 31
LET => reduce 31
VAL => reduce 31
IN => reduce 31
BY => reduce 31
LSQUARE => reduce 31
RSQUARE => reduce 31
LPAREN => reduce 31
RPAREN => reduce 31
COMMA => reduce 31
SEMI => reduce 31
BEGIN => reduce 31
END => reduce 31
IDENT => reduce 31
PROVE => reduce 31
PROJ1 => reduce 31
PROJ2 => reduce 31
BACKTICK => reduce 31
REFINE => reduce 31
GOAL => reduce 31
PUSH => reduce 31
PRINT => reduce 31
EXACT => reduce 31

-----

State 28:

10 : Atm -> BACKTICK OExp .  / 4

$ => reduce 10
LET => reduce 10
VAL => reduce 10
IN => reduce 10
BY => reduce 10
RSQUARE => reduce 10
LPAREN => reduce 10
RPAREN => reduce 10
COMMA => reduce 10
SEMI => reduce 10
BEGIN => reduce 10
END => reduce 10
IDENT => reduce 10
PROVE => reduce 10
PROJ1 => reduce 10
PROJ2 => reduce 10
BACKTICK => reduce 10
REFINE => reduce 10
GOAL => reduce 10
PUSH => reduce 10
PRINT => reduce 10
EXACT => reduce 10

-----

State 29:

3 : Atm -> LPAREN Exp . COMMA Exp RPAREN  / 4
8 : Atm -> LPAREN Exp . RPAREN  / 4

RPAREN => shift 46
COMMA => shift 47

-----

State 30:

2 : Atm -> LPAREN RPAREN .  / 4

$ => reduce 2
LET => reduce 2
VAL => reduce 2
IN => reduce 2
BY => reduce 2
RSQUARE => reduce 2
LPAREN => reduce 2
RPAREN => reduce 2
COMMA => reduce 2
SEMI => reduce 2
BEGIN => reduce 2
END => reduce 2
IDENT => reduce 2
PROVE => reduce 2
PROJ1 => reduce 2
PROJ2 => reduce 2
BACKTICK => reduce 2
REFINE => reduce 2
GOAL => reduce 2
PUSH => reduce 2
PRINT => reduce 2
EXACT => reduce 2

-----

State 31:

9 : Atm -> BEGIN Exp . END  / 4

END => shift 48

-----

State 32:

7 : Atm -> PROVE Exp . BY Exp END  / 4

BY => shift 49

-----

State 33:

11 : Atm -> REFINE IDENT .  / 4

$ => reduce 11
LET => reduce 11
VAL => reduce 11
IN => reduce 11
BY => reduce 11
RSQUARE => reduce 11
LPAREN => reduce 11
RPAREN => reduce 11
COMMA => reduce 11
SEMI => reduce 11
BEGIN => reduce 11
END => reduce 11
IDENT => reduce 11
PROVE => reduce 11
PROJ1 => reduce 11
PROJ2 => reduce 11
BACKTICK => reduce 11
REFINE => reduce 11
GOAL => reduce 11
PUSH => reduce 11
PRINT => reduce 11
EXACT => reduce 11

-----

State 34:

28 : Names -> IDENT . COMMA Names  / 6
29 : Names -> IDENT .  / 6

IN => reduce 29
COMMA => shift 50

-----

State 35:

13 : Atm -> PUSH Names . IN Exp END  / 4

IN => shift 51

-----

State 36:

12 : Atm -> EXACT Atm .  / 4

$ => reduce 12
LET => reduce 12
VAL => reduce 12
IN => reduce 12
BY => reduce 12
RSQUARE => reduce 12
LPAREN => reduce 12
RPAREN => reduce 12
COMMA => reduce 12
SEMI => reduce 12
BEGIN => reduce 12
END => reduce 12
IDENT => reduce 12
PROVE => reduce 12
PROJ1 => reduce 12
PROJ2 => reduce 12
BACKTICK => reduce 12
REFINE => reduce 12
GOAL => reduce 12
PUSH => reduce 12
PRINT => reduce 12
EXACT => reduce 12

-----

State 37:

0 : Atm -> . IDENT  / 4
1 : Atm -> . GOAL  / 4
2 : Atm -> . LPAREN RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 4
5 : Atm -> . PROJ2  / 4
6 : Atm -> . LET Decls IN Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 4
11 : Atm -> . REFINE IDENT  / 4
12 : Atm -> . EXACT Atm  / 4
13 : Atm -> . PUSH Names IN Exp END  / 4
14 : Atm -> . PRINT Atm  / 4
18 : App -> . Atm  / 4
19 : App -> . App Atm  / 4
21 : SeqExp -> SeqExp SEMI . App  / 7
22 : SeqExp -> SeqExp SEMI . LSQUARE Exps RSQUARE  / 7

LET => shift 2
LSQUARE => shift 52
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Atm => goto 17
App => goto 53

-----

State 38:

0 : Atm -> . IDENT  / 4
1 : Atm -> . GOAL  / 4
2 : Atm -> . LPAREN RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 4
5 : Atm -> . PROJ2  / 4
6 : Atm -> . LET Decls IN Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 4
11 : Atm -> . REFINE IDENT  / 4
12 : Atm -> . EXACT Atm  / 4
13 : Atm -> . PUSH Names IN Exp END  / 4
14 : Atm -> . PRINT Atm  / 4
18 : App -> . Atm  / 4
19 : App -> . App Atm  / 4
20 : SeqExp -> . App  / 7
21 : SeqExp -> . SeqExp SEMI App  / 7
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 7
23 : Exp -> . SeqExp  / 3
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 3
24 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW . Exp  / 3

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 54
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 39:

16 : Decls -> Decl Decls .  / 6

IN => reduce 16

-----

State 40:

0 : Atm -> . IDENT  / 11
1 : Atm -> . GOAL  / 11
2 : Atm -> . LPAREN RPAREN  / 11
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 11
4 : Atm -> . PROJ1  / 11
5 : Atm -> . PROJ2  / 11
6 : Atm -> . LET Decls IN Exp END  / 11
6 : Atm -> LET Decls IN . Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 11
8 : Atm -> . LPAREN Exp RPAREN  / 11
9 : Atm -> . BEGIN Exp END  / 11
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . PUSH Names IN Exp END  / 11
14 : Atm -> . PRINT Atm  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : SeqExp -> . App  / 12
21 : SeqExp -> . SeqExp SEMI App  / 12
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 12
23 : Exp -> . SeqExp  / 13
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 13

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 55
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 41:

15 : Decl -> VAL IDENT . EQUALS Exp  / 5

EQUALS => shift 56

-----

State 42:

36 : OIdents -> . IDENT OIdents  / 18
36 : OIdents -> IDENT . OIdents  / 18
37 : OIdents -> .  / 18

RSQUARE => reduce 37
IDENT => shift 42
OIdents => goto 57

-----

State 43:

33 : OExp -> LSQUARE OIdents . RSQUARE  / 17

RSQUARE => shift 58

-----

State 44:

31 : OExp -> . IDENT  / 19
32 : OExp -> . LPAREN OExps RPAREN  / 19
33 : OExp -> . LSQUARE OIdents RSQUARE  / 19
34 : OExps -> . OExp OExps  / 20
34 : OExps -> OExp . OExps  / 20
35 : OExps -> .  / 20

LSQUARE => shift 25
LPAREN => shift 26
RPAREN => reduce 35
IDENT => shift 27
OExp => goto 44
OExps => goto 59

-----

State 45:

32 : OExp -> LPAREN OExps . RPAREN  / 17

RPAREN => shift 60

-----

State 46:

8 : Atm -> LPAREN Exp RPAREN .  / 4

$ => reduce 8
LET => reduce 8
VAL => reduce 8
IN => reduce 8
BY => reduce 8
RSQUARE => reduce 8
LPAREN => reduce 8
RPAREN => reduce 8
COMMA => reduce 8
SEMI => reduce 8
BEGIN => reduce 8
END => reduce 8
IDENT => reduce 8
PROVE => reduce 8
PROJ1 => reduce 8
PROJ2 => reduce 8
BACKTICK => reduce 8
REFINE => reduce 8
GOAL => reduce 8
PUSH => reduce 8
PRINT => reduce 8
EXACT => reduce 8

-----

State 47:

0 : Atm -> . IDENT  / 21
1 : Atm -> . GOAL  / 21
2 : Atm -> . LPAREN RPAREN  / 21
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 21
3 : Atm -> LPAREN Exp COMMA . Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 21
5 : Atm -> . PROJ2  / 21
6 : Atm -> . LET Decls IN Exp END  / 21
7 : Atm -> . PROVE Exp BY Exp END  / 21
8 : Atm -> . LPAREN Exp RPAREN  / 21
9 : Atm -> . BEGIN Exp END  / 21
10 : Atm -> . BACKTICK OExp  / 21
11 : Atm -> . REFINE IDENT  / 21
12 : Atm -> . EXACT Atm  / 21
13 : Atm -> . PUSH Names IN Exp END  / 21
14 : Atm -> . PRINT Atm  / 21
18 : App -> . Atm  / 21
19 : App -> . App Atm  / 21
20 : SeqExp -> . App  / 22
21 : SeqExp -> . SeqExp SEMI App  / 22
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 22
23 : Exp -> . SeqExp  / 20
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 20

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 61
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 48:

9 : Atm -> BEGIN Exp END .  / 4

$ => reduce 9
LET => reduce 9
VAL => reduce 9
IN => reduce 9
BY => reduce 9
RSQUARE => reduce 9
LPAREN => reduce 9
RPAREN => reduce 9
COMMA => reduce 9
SEMI => reduce 9
BEGIN => reduce 9
END => reduce 9
IDENT => reduce 9
PROVE => reduce 9
PROJ1 => reduce 9
PROJ2 => reduce 9
BACKTICK => reduce 9
REFINE => reduce 9
GOAL => reduce 9
PUSH => reduce 9
PRINT => reduce 9
EXACT => reduce 9

-----

State 49:

0 : Atm -> . IDENT  / 11
1 : Atm -> . GOAL  / 11
2 : Atm -> . LPAREN RPAREN  / 11
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 11
4 : Atm -> . PROJ1  / 11
5 : Atm -> . PROJ2  / 11
6 : Atm -> . LET Decls IN Exp END  / 11
7 : Atm -> . PROVE Exp BY Exp END  / 11
7 : Atm -> PROVE Exp BY . Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 11
9 : Atm -> . BEGIN Exp END  / 11
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . PUSH Names IN Exp END  / 11
14 : Atm -> . PRINT Atm  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : SeqExp -> . App  / 12
21 : SeqExp -> . SeqExp SEMI App  / 12
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 12
23 : Exp -> . SeqExp  / 13
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 13

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 62
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 50:

28 : Names -> . IDENT COMMA Names  / 6
28 : Names -> IDENT COMMA . Names  / 6
29 : Names -> . IDENT  / 6
30 : Names -> .  / 6

IN => reduce 30
IDENT => shift 34
Names => goto 63

-----

State 51:

0 : Atm -> . IDENT  / 11
1 : Atm -> . GOAL  / 11
2 : Atm -> . LPAREN RPAREN  / 11
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 11
4 : Atm -> . PROJ1  / 11
5 : Atm -> . PROJ2  / 11
6 : Atm -> . LET Decls IN Exp END  / 11
7 : Atm -> . PROVE Exp BY Exp END  / 11
8 : Atm -> . LPAREN Exp RPAREN  / 11
9 : Atm -> . BEGIN Exp END  / 11
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . PUSH Names IN Exp END  / 11
13 : Atm -> PUSH Names IN . Exp END  / 4
14 : Atm -> . PRINT Atm  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : SeqExp -> . App  / 12
21 : SeqExp -> . SeqExp SEMI App  / 12
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 12
23 : Exp -> . SeqExp  / 13
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 13

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 64
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 52:

0 : Atm -> . IDENT  / 23
1 : Atm -> . GOAL  / 23
2 : Atm -> . LPAREN RPAREN  / 23
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 23
4 : Atm -> . PROJ1  / 23
5 : Atm -> . PROJ2  / 23
6 : Atm -> . LET Decls IN Exp END  / 23
7 : Atm -> . PROVE Exp BY Exp END  / 23
8 : Atm -> . LPAREN Exp RPAREN  / 23
9 : Atm -> . BEGIN Exp END  / 23
10 : Atm -> . BACKTICK OExp  / 23
11 : Atm -> . REFINE IDENT  / 23
12 : Atm -> . EXACT Atm  / 23
13 : Atm -> . PUSH Names IN Exp END  / 23
14 : Atm -> . PRINT Atm  / 23
18 : App -> . Atm  / 23
19 : App -> . App Atm  / 23
20 : SeqExp -> . App  / 24
21 : SeqExp -> . SeqExp SEMI App  / 24
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 24
22 : SeqExp -> SeqExp SEMI LSQUARE . Exps RSQUARE  / 7
23 : Exp -> . SeqExp  / 25
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 25
25 : Exps -> . Exp COMMA Exps  / 18
26 : Exps -> . Exp  / 18
27 : Exps -> .  / 18

LET => shift 2
FN => shift 1
RSQUARE => reduce 27
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 65
Atm => goto 17
App => goto 3
SeqExp => goto 18
Exps => goto 66

-----

State 53:

0 : Atm -> . IDENT  / 4
1 : Atm -> . GOAL  / 4
2 : Atm -> . LPAREN RPAREN  / 4
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 4
4 : Atm -> . PROJ1  / 4
5 : Atm -> . PROJ2  / 4
6 : Atm -> . LET Decls IN Exp END  / 4
7 : Atm -> . PROVE Exp BY Exp END  / 4
8 : Atm -> . LPAREN Exp RPAREN  / 4
9 : Atm -> . BEGIN Exp END  / 4
10 : Atm -> . BACKTICK OExp  / 4
11 : Atm -> . REFINE IDENT  / 4
12 : Atm -> . EXACT Atm  / 4
13 : Atm -> . PUSH Names IN Exp END  / 4
14 : Atm -> . PRINT Atm  / 4
19 : App -> App . Atm  / 4
21 : SeqExp -> SeqExp SEMI App .  / 7

$ => reduce 21
LET => shift 2
VAL => reduce 21
IN => reduce 21
BY => reduce 21
RSQUARE => reduce 21
LPAREN => shift 8
RPAREN => reduce 21
COMMA => reduce 21
SEMI => reduce 21
BEGIN => shift 9
END => reduce 21
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Atm => goto 23

-----

State 54:

24 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW Exp .  / 3

$ => reduce 24
VAL => reduce 24
IN => reduce 24
BY => reduce 24
RSQUARE => reduce 24
RPAREN => reduce 24
COMMA => reduce 24
END => reduce 24

-----

State 55:

6 : Atm -> LET Decls IN Exp . END  / 4

END => shift 67

-----

State 56:

0 : Atm -> . IDENT  / 26
1 : Atm -> . GOAL  / 26
2 : Atm -> . LPAREN RPAREN  / 26
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 26
4 : Atm -> . PROJ1  / 26
5 : Atm -> . PROJ2  / 26
6 : Atm -> . LET Decls IN Exp END  / 26
7 : Atm -> . PROVE Exp BY Exp END  / 26
8 : Atm -> . LPAREN Exp RPAREN  / 26
9 : Atm -> . BEGIN Exp END  / 26
10 : Atm -> . BACKTICK OExp  / 26
11 : Atm -> . REFINE IDENT  / 26
12 : Atm -> . EXACT Atm  / 26
13 : Atm -> . PUSH Names IN Exp END  / 26
14 : Atm -> . PRINT Atm  / 26
15 : Decl -> VAL IDENT EQUALS . Exp  / 5
18 : App -> . Atm  / 26
19 : App -> . App Atm  / 26
20 : SeqExp -> . App  / 27
21 : SeqExp -> . SeqExp SEMI App  / 27
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 27
23 : Exp -> . SeqExp  / 5
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 5

LET => shift 2
FN => shift 1
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 68
Atm => goto 17
App => goto 3
SeqExp => goto 18

-----

State 57:

36 : OIdents -> IDENT OIdents .  / 18

RSQUARE => reduce 36

-----

State 58:

33 : OExp -> LSQUARE OIdents RSQUARE .  / 17

$ => reduce 33
LET => reduce 33
VAL => reduce 33
IN => reduce 33
BY => reduce 33
LSQUARE => reduce 33
RSQUARE => reduce 33
LPAREN => reduce 33
RPAREN => reduce 33
COMMA => reduce 33
SEMI => reduce 33
BEGIN => reduce 33
END => reduce 33
IDENT => reduce 33
PROVE => reduce 33
PROJ1 => reduce 33
PROJ2 => reduce 33
BACKTICK => reduce 33
REFINE => reduce 33
GOAL => reduce 33
PUSH => reduce 33
PRINT => reduce 33
EXACT => reduce 33

-----

State 59:

34 : OExps -> OExp OExps .  / 20

RPAREN => reduce 34

-----

State 60:

32 : OExp -> LPAREN OExps RPAREN .  / 17

$ => reduce 32
LET => reduce 32
VAL => reduce 32
IN => reduce 32
BY => reduce 32
LSQUARE => reduce 32
RSQUARE => reduce 32
LPAREN => reduce 32
RPAREN => reduce 32
COMMA => reduce 32
SEMI => reduce 32
BEGIN => reduce 32
END => reduce 32
IDENT => reduce 32
PROVE => reduce 32
PROJ1 => reduce 32
PROJ2 => reduce 32
BACKTICK => reduce 32
REFINE => reduce 32
GOAL => reduce 32
PUSH => reduce 32
PRINT => reduce 32
EXACT => reduce 32

-----

State 61:

3 : Atm -> LPAREN Exp COMMA Exp . RPAREN  / 4

RPAREN => shift 69

-----

State 62:

7 : Atm -> PROVE Exp BY Exp . END  / 4

END => shift 70

-----

State 63:

28 : Names -> IDENT COMMA Names .  / 6

IN => reduce 28

-----

State 64:

13 : Atm -> PUSH Names IN Exp . END  / 4

END => shift 71

-----

State 65:

25 : Exps -> Exp . COMMA Exps  / 18
26 : Exps -> Exp .  / 18

RSQUARE => reduce 26
COMMA => shift 72

-----

State 66:

22 : SeqExp -> SeqExp SEMI LSQUARE Exps . RSQUARE  / 7

RSQUARE => shift 73

-----

State 67:

6 : Atm -> LET Decls IN Exp END .  / 4

$ => reduce 6
LET => reduce 6
VAL => reduce 6
IN => reduce 6
BY => reduce 6
RSQUARE => reduce 6
LPAREN => reduce 6
RPAREN => reduce 6
COMMA => reduce 6
SEMI => reduce 6
BEGIN => reduce 6
END => reduce 6
IDENT => reduce 6
PROVE => reduce 6
PROJ1 => reduce 6
PROJ2 => reduce 6
BACKTICK => reduce 6
REFINE => reduce 6
GOAL => reduce 6
PUSH => reduce 6
PRINT => reduce 6
EXACT => reduce 6

-----

State 68:

15 : Decl -> VAL IDENT EQUALS Exp .  / 5

VAL => reduce 15
IN => reduce 15

-----

State 69:

3 : Atm -> LPAREN Exp COMMA Exp RPAREN .  / 4

$ => reduce 3
LET => reduce 3
VAL => reduce 3
IN => reduce 3
BY => reduce 3
RSQUARE => reduce 3
LPAREN => reduce 3
RPAREN => reduce 3
COMMA => reduce 3
SEMI => reduce 3
BEGIN => reduce 3
END => reduce 3
IDENT => reduce 3
PROVE => reduce 3
PROJ1 => reduce 3
PROJ2 => reduce 3
BACKTICK => reduce 3
REFINE => reduce 3
GOAL => reduce 3
PUSH => reduce 3
PRINT => reduce 3
EXACT => reduce 3

-----

State 70:

7 : Atm -> PROVE Exp BY Exp END .  / 4

$ => reduce 7
LET => reduce 7
VAL => reduce 7
IN => reduce 7
BY => reduce 7
RSQUARE => reduce 7
LPAREN => reduce 7
RPAREN => reduce 7
COMMA => reduce 7
SEMI => reduce 7
BEGIN => reduce 7
END => reduce 7
IDENT => reduce 7
PROVE => reduce 7
PROJ1 => reduce 7
PROJ2 => reduce 7
BACKTICK => reduce 7
REFINE => reduce 7
GOAL => reduce 7
PUSH => reduce 7
PRINT => reduce 7
EXACT => reduce 7

-----

State 71:

13 : Atm -> PUSH Names IN Exp END .  / 4

$ => reduce 13
LET => reduce 13
VAL => reduce 13
IN => reduce 13
BY => reduce 13
RSQUARE => reduce 13
LPAREN => reduce 13
RPAREN => reduce 13
COMMA => reduce 13
SEMI => reduce 13
BEGIN => reduce 13
END => reduce 13
IDENT => reduce 13
PROVE => reduce 13
PROJ1 => reduce 13
PROJ2 => reduce 13
BACKTICK => reduce 13
REFINE => reduce 13
GOAL => reduce 13
PUSH => reduce 13
PRINT => reduce 13
EXACT => reduce 13

-----

State 72:

0 : Atm -> . IDENT  / 23
1 : Atm -> . GOAL  / 23
2 : Atm -> . LPAREN RPAREN  / 23
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 23
4 : Atm -> . PROJ1  / 23
5 : Atm -> . PROJ2  / 23
6 : Atm -> . LET Decls IN Exp END  / 23
7 : Atm -> . PROVE Exp BY Exp END  / 23
8 : Atm -> . LPAREN Exp RPAREN  / 23
9 : Atm -> . BEGIN Exp END  / 23
10 : Atm -> . BACKTICK OExp  / 23
11 : Atm -> . REFINE IDENT  / 23
12 : Atm -> . EXACT Atm  / 23
13 : Atm -> . PUSH Names IN Exp END  / 23
14 : Atm -> . PRINT Atm  / 23
18 : App -> . Atm  / 23
19 : App -> . App Atm  / 23
20 : SeqExp -> . App  / 24
21 : SeqExp -> . SeqExp SEMI App  / 24
22 : SeqExp -> . SeqExp SEMI LSQUARE Exps RSQUARE  / 24
23 : Exp -> . SeqExp  / 25
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 25
25 : Exps -> . Exp COMMA Exps  / 18
25 : Exps -> Exp COMMA . Exps  / 18
26 : Exps -> . Exp  / 18
27 : Exps -> .  / 18

LET => shift 2
FN => shift 1
RSQUARE => reduce 27
LPAREN => shift 8
BEGIN => shift 9
IDENT => shift 11
PROVE => shift 10
PROJ1 => shift 13
PROJ2 => shift 12
BACKTICK => shift 7
REFINE => shift 14
GOAL => shift 6
PUSH => shift 15
PRINT => shift 5
EXACT => shift 16
Exp => goto 65
Atm => goto 17
App => goto 3
SeqExp => goto 18
Exps => goto 74

-----

State 73:

22 : SeqExp -> SeqExp SEMI LSQUARE Exps RSQUARE .  / 7

$ => reduce 22
VAL => reduce 22
IN => reduce 22
BY => reduce 22
RSQUARE => reduce 22
RPAREN => reduce 22
COMMA => reduce 22
SEMI => reduce 22
END => reduce 22

-----

State 74:

25 : Exps -> Exp COMMA Exps .  / 18

RSQUARE => reduce 25

-----

lookahead 0 = $ 
lookahead 1 = $ LET LPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 2 = $ SEMI 
lookahead 3 = $ VAL IN BY RSQUARE RPAREN COMMA END 
lookahead 4 = $ LET VAL IN BY RSQUARE LPAREN RPAREN COMMA SEMI BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 5 = VAL IN 
lookahead 6 = IN 
lookahead 7 = $ VAL IN BY RSQUARE RPAREN COMMA SEMI END 
lookahead 8 = LET LPAREN RPAREN COMMA SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 9 = RPAREN COMMA SEMI 
lookahead 10 = RPAREN COMMA 
lookahead 11 = LET LPAREN SEMI BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 12 = SEMI END 
lookahead 13 = END 
lookahead 14 = LET BY LPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 15 = BY SEMI 
lookahead 16 = BY 
lookahead 17 = $ LET VAL IN BY LSQUARE RSQUARE LPAREN RPAREN COMMA SEMI BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 18 = RSQUARE 
lookahead 19 = LSQUARE LPAREN RPAREN IDENT 
lookahead 20 = RPAREN 
lookahead 21 = LET LPAREN RPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 22 = RPAREN SEMI 
lookahead 23 = LET RSQUARE LPAREN COMMA SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 24 = RSQUARE COMMA SEMI 
lookahead 25 = RSQUARE COMMA 
lookahead 26 = LET VAL IN LPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 27 = VAL IN SEMI 

*)

struct
local
structure Value = struct
datatype nonterminal =
nonterminal
| pos of Arg.pos
| pos_string of Arg.pos_string
| exp of Arg.exp
| decl of Arg.decl
| decls of Arg.decls
| exps of Arg.exps
| names of Arg.names
| oexp of Arg.oexp
| oexps of Arg.oexps
end
structure ParseEngine = ParseEngineFun (structure Streamable = Streamable
type terminal = Arg.terminal
type value = Value.nonterminal
val dummy = Value.nonterminal
fun read terminal =
(case terminal of
Arg.LET x => (1, Value.pos x)
| Arg.FN x => (2, Value.pos x)
| Arg.VAL x => (3, Value.pos x)
| Arg.IN x => (4, Value.pos x)
| Arg.BY x => (5, Value.pos x)
| Arg.DOUBLE_RIGHT_ARROW x => (6, Value.pos x)
| Arg.LSQUARE x => (7, Value.pos x)
| Arg.RSQUARE x => (8, Value.pos x)
| Arg.LPAREN x => (9, Value.pos x)
| Arg.RPAREN x => (10, Value.pos x)
| Arg.COMMA x => (11, Value.pos x)
| Arg.SEMI x => (12, Value.pos x)
| Arg.EQUALS x => (13, Value.pos x)
| Arg.BEGIN x => (14, Value.pos x)
| Arg.END x => (15, Value.pos x)
| Arg.IDENT x => (16, Value.pos_string x)
| Arg.PROVE x => (17, Value.pos x)
| Arg.PROJ1 x => (18, Value.pos x)
| Arg.PROJ2 x => (19, Value.pos x)
| Arg.BACKTICK x => (20, Value.pos x)
| Arg.REFINE x => (21, Value.pos x)
| Arg.GOAL x => (22, Value.pos x)
| Arg.PUSH x => (23, Value.pos x)
| Arg.PRINT x => (24, Value.pos x)
| Arg.EXACT x => (25, Value.pos x)
)
)
in
val parse = ParseEngine.parse (
ParseEngine.next5x1 "\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151m\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128j\131\128jjj\128\128j\137jjj\128\138j\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\127\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\128\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128}}\128}}}\128\128}}}}}\128}}}}}}}}}}}}\128\128\128\128\128\128\128\128\128\128\128\128\128\154\128\155\128\128\128\128\128\128\156\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\159\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128~~\128~~~\128\128~~~~~\128~~~~~~~~~~~~\128\128\128\128\128\128yy\128yyy\128\128yyyyy\128yyyyyyyyyyyy\128\128\128\128\128\128zz\128zzz\128\128zzzzz\128zzzzzzzzzzzz\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\162\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128`\128\128\128\128\128\128\128\128\128\128\128\163\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\128\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128ll\128lll\128\128lllll\128llllllllllll\128\128\128\128\128\128g\128\128ggg\128\128g\128gg\166\128\128g\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\167\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151m\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\169\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\170\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128kk\128kkk\128\128kkkkk\128kkkkkkkkkkkk\128\128\128\128\128\128pp\128ppp\128\128ppppp\128pppppppppppp\128\128\128\128\128\128\128\128\128\128\128\128\128\128Y\128\128\128\128\128\128\128\171\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\154\128\155[\128\128\128\128\128\156\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128__\128___\128______\128____________\128\128\128\128\128\128tt\128ttt\128\128ttttt\128tttttttttttt\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\175\176\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128||\128|||\128\128|||||\128||||||||||||\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\177\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\178\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128ss\128sss\128\128sssss\128ssssssssssss\128\128\128\128\128\128\128\128\128\128a\128\128\128\128\128\128\179\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\180\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128rr\128rrr\128\128rrrrr\128rrrrrrrrrrrr\128\128\128\128\128\128\128\131\128\128\128\128\128\181\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\128\128\128n\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\185\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128Y\128\128\128\128\128\128\128\171\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\187\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\154\128\155[\128\128\128\128\128\156\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\189\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128vv\128vvv\128\128vvvvv\128vvvvvvvvvvvv\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128uu\128uuu\128\128uuuuu\128uuuuuuuuuuuu\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\128\128\128`\128\128\128\128\128\128\128\128\128\128\128\163\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\131\130\128\128\128\128\128c\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128i\131\128iii\128\128i\137iii\128\138i\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128f\128\128fff\128\128f\128ff\128\128\128f\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\196\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\128\128\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128\128\128\128\128\128\128\128\128Z\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128]]\128]]]\128]]]]]]\128]]]]]]]]]]]]\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\\\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128^^\128^^^\128^^^^^^\128^^^^^^^^^^^^\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\198\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\199\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128b\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\200\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128d\128\128\201\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\202\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128xx\128xxx\128\128xxxxx\128xxxxxxxxxxxx\128\128\128\128\128\128\128\128\128oo\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128{{\128{{{\128\128{{{{{\128{{{{{{{{{{{{\128\128\128\128\128\128ww\128www\128\128wwwww\128wwwwwwwwwwww\128\128\128\128\128\128qq\128qqq\128\128qqqqq\128qqqqqqqqqqqq\128\128\128\128\128\128\128\131\130\128\128\128\128\128c\137\128\128\128\128\138\128\140\139\142\141\136\143\135\144\134\145\128\128\128\128\128\128h\128\128hhh\128\128h\128hhh\128\128h\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128e\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
ParseEngine.next5x1 "\132\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\149\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\152\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\156\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\157\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\159\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\160\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\163\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\164\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\167\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\171\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\172\128\128\128\128\128\173\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\145\128\128\128\128\181\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\182\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\183\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\185\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\172\128\128\128\128\128\187\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\189\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\190\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\191\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\192\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\193\145\128\128\128\128\131\146\194\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\196\145\128\128\128\128\131\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\193\145\128\128\128\128\131\146\202\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
Vector.fromList [(1,1,(fn Value.pos_string(arg0)::rest => Value.exp(Arg.var arg0)::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.goal arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.pos(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.nil_ {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.pair {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.proj1 arg0)::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.proj2 arg0)::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.decls(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.let_ {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.prove {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn _::Value.exp(arg0)::_::rest => Value.exp(Arg.identity arg0)::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn _::Value.exp(arg0)::_::rest => Value.exp(Arg.identity arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.oexp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.quote {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.pos_string(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.refine {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.exp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.exact {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.names(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.push {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.exp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.print {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(5,4,(fn Value.exp(arg0)::_::Value.pos_string(arg1)::_::rest => Value.decl(Arg.declVal {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(2,2,(fn Value.decls(arg0)::Value.decl(arg1)::rest => Value.decls(Arg.declsCons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(2,0,(fn rest => Value.decls(Arg.declsNil {})::rest)),
(6,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.identity arg0)::rest|_=>raise (Fail "bad parser"))),
(6,2,(fn Value.exp(arg0)::Value.exp(arg1)::rest => Value.exp(Arg.app {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(7,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.identity arg0)::rest|_=>raise (Fail "bad parser"))),
(7,3,(fn Value.exp(arg0)::_::Value.exp(arg1)::rest => Value.exp(Arg.seqExpSnoc {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(7,5,(fn Value.pos(arg0)::Value.exps(arg1)::_::_::Value.exp(arg2)::rest => Value.exp(Arg.seqExpSnocFork {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(0,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.identity arg0)::rest|_=>raise (Fail "bad parser"))),
(0,4,(fn Value.exp(arg0)::_::Value.pos_string(arg1)::Value.pos(arg2)::rest => Value.exp(Arg.fn_ {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(8,3,(fn Value.exps(arg0)::_::Value.exp(arg1)::rest => Value.exps(Arg.expsCons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(8,1,(fn Value.exp(arg0)::rest => Value.exps(Arg.expsSingl arg0)::rest|_=>raise (Fail "bad parser"))),
(8,0,(fn rest => Value.exps(Arg.expsNil {})::rest)),
(4,3,(fn Value.names(arg0)::_::Value.pos_string(arg1)::rest => Value.names(Arg.namesCons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(4,1,(fn Value.pos_string(arg0)::rest => Value.names(Arg.namesSingl arg0)::rest|_=>raise (Fail "bad parser"))),
(4,0,(fn rest => Value.names(Arg.namesNil {})::rest)),
(3,1,(fn Value.pos_string(arg0)::rest => Value.oexp(Arg.oident arg0)::rest|_=>raise (Fail "bad parser"))),
(3,3,(fn Value.pos(arg0)::Value.oexps(arg1)::Value.pos(arg2)::rest => Value.oexp(Arg.ogroup {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(3,3,(fn Value.pos(arg0)::Value.names(arg1)::Value.pos(arg2)::rest => Value.oexp(Arg.obinding {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(9,2,(fn Value.oexps(arg0)::Value.oexp(arg1)::rest => Value.oexps(Arg.oexpsCons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(9,0,(fn rest => Value.oexps(Arg.oexpsNil {})::rest)),
(10,2,(fn Value.names(arg0)::Value.pos_string(arg1)::rest => Value.names(Arg.namesCons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(10,0,(fn rest => Value.names(Arg.namesNil {})::rest))],
(fn Value.exp x => x | _ => raise (Fail "bad parser")), Arg.error)
end
end
