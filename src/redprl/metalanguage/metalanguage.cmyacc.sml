
functor MetalanguageParseFn
   (structure Streamable : STREAMABLE
    structure Arg :
       sig
          type pos
          type pos_string
          type exp
          type exps
          type names
          type oexp

          val obool : pos -> oexp
          val names_nil : unit -> names
          val names_singl : pos_string -> names
          val names_cons : pos_string * names -> names
          val exp_nil : unit -> exps
          val exp_singl : exp -> exps
          val exp_cons : exp * exps -> exps
          val fn_ : pos * pos_string * exp -> exp
          val print : pos * exp -> exp
          val app_exp : exp -> exp
          val app : exp * exp -> exp
          val atm_app : exp -> exp
          val push : pos * names * exp * pos -> exp
          val fork : pos * exps * pos -> exp
          val refine : pos * pos_string -> exp
          val quote : pos * oexp -> exp
          val exp_atm : exp -> exp
          val prove : pos * exp * exp * pos -> exp
          val let_ : pos * pos_string * exp * exp * pos -> exp
          val proj2 : pos -> exp
          val proj1 : pos -> exp
          val pair : pos * exp * exp * pos -> exp
          val nil_ : pos * pos -> exp
          val goal : pos -> exp
          val var : pos_string -> exp

          datatype terminal =
             LET of pos
           | FN of pos
           | IN of pos
           | DOUBLE_RIGHT_ARROW of pos
           | LSQUARE of pos
           | RSQUARE of pos
           | LPAREN of pos
           | RPAREN of pos
           | COMMA of pos
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
           | BOOL of pos

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
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 1
7 : Atm -> . PROVE Exp IN Exp END  / 1
8 : Atm -> . LPAREN Exp RPAREN  / 1
9 : Atm -> . BEGIN Exp END  / 1
10 : Atm -> . BACKTICK OExp  / 1
11 : Atm -> . REFINE IDENT  / 1
12 : Atm -> . LSQUARE Exps RSQUARE  / 1
13 : Atm -> . PUSH Names IN Exp END  / 1
14 : App -> . Atm  / 1
15 : App -> . App Atm  / 1
16 : Exp -> . App  / 0
17 : Exp -> . PRINT Atm  / 0
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 0

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 16
Atm => goto 17
App => goto 15

-----

State 1:

18 : Exp -> FN . IDENT DOUBLE_RIGHT_ARROW Exp  / 2

IDENT => shift 18

-----

State 2:

6 : Atm -> LET . IDENT EQUALS Exp IN Exp END  / 3

IDENT => shift 19

-----

State 3:

13 : Atm -> PUSH . Names IN Exp END  / 3
22 : Names -> . IDENT COMMA Names  / 4
23 : Names -> . IDENT  / 4
24 : Names -> .  / 4

IN => reduce 24
IDENT => shift 20
Names => goto 21

-----

State 4:

0 : Atm -> . IDENT  / 5
1 : Atm -> . GOAL  / 5
2 : Atm -> . LPAREN RPAREN  / 5
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 5
4 : Atm -> . PROJ1  / 5
5 : Atm -> . PROJ2  / 5
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 5
7 : Atm -> . PROVE Exp IN Exp END  / 5
8 : Atm -> . LPAREN Exp RPAREN  / 5
9 : Atm -> . BEGIN Exp END  / 5
10 : Atm -> . BACKTICK OExp  / 5
11 : Atm -> . REFINE IDENT  / 5
12 : Atm -> . LSQUARE Exps RSQUARE  / 5
12 : Atm -> LSQUARE . Exps RSQUARE  / 3
13 : Atm -> . PUSH Names IN Exp END  / 5
14 : App -> . Atm  / 5
15 : App -> . App Atm  / 5
16 : Exp -> . App  / 6
17 : Exp -> . PRINT Atm  / 6
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 6
19 : Exps -> . Exp COMMA Exps  / 7
20 : Exps -> . Exp  / 7
21 : Exps -> .  / 7

LET => shift 2
FN => shift 1
LSQUARE => shift 4
RSQUARE => reduce 21
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 22
Atm => goto 17
Exps => goto 23
App => goto 15

-----

State 5:

10 : Atm -> BACKTICK . OExp  / 3
25 : OExp -> . BOOL  / 3

BOOL => shift 24
OExp => goto 25

-----

State 6:

0 : Atm -> . IDENT  / 8
1 : Atm -> . GOAL  / 8
2 : Atm -> . LPAREN RPAREN  / 8
2 : Atm -> LPAREN . RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 8
3 : Atm -> LPAREN . Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 8
5 : Atm -> . PROJ2  / 8
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 8
7 : Atm -> . PROVE Exp IN Exp END  / 8
8 : Atm -> . LPAREN Exp RPAREN  / 8
8 : Atm -> LPAREN . Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 8
10 : Atm -> . BACKTICK OExp  / 8
11 : Atm -> . REFINE IDENT  / 8
12 : Atm -> . LSQUARE Exps RSQUARE  / 8
13 : Atm -> . PUSH Names IN Exp END  / 8
14 : App -> . Atm  / 8
15 : App -> . App Atm  / 8
16 : Exp -> . App  / 9
17 : Exp -> . PRINT Atm  / 9
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 9

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
RPAREN => shift 26
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 27
Atm => goto 17
App => goto 15

-----

State 7:

0 : Atm -> . IDENT  / 10
1 : Atm -> . GOAL  / 10
2 : Atm -> . LPAREN RPAREN  / 10
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 10
4 : Atm -> . PROJ1  / 10
5 : Atm -> . PROJ2  / 10
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 10
7 : Atm -> . PROVE Exp IN Exp END  / 10
8 : Atm -> . LPAREN Exp RPAREN  / 10
9 : Atm -> . BEGIN Exp END  / 10
9 : Atm -> BEGIN . Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 10
11 : Atm -> . REFINE IDENT  / 10
12 : Atm -> . LSQUARE Exps RSQUARE  / 10
13 : Atm -> . PUSH Names IN Exp END  / 10
14 : App -> . Atm  / 10
15 : App -> . App Atm  / 10
16 : Exp -> . App  / 11
17 : Exp -> . PRINT Atm  / 11
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 11

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 28
Atm => goto 17
App => goto 15

-----

State 8:

0 : Atm -> . IDENT  / 12
1 : Atm -> . GOAL  / 12
2 : Atm -> . LPAREN RPAREN  / 12
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 12
4 : Atm -> . PROJ1  / 12
5 : Atm -> . PROJ2  / 12
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 12
7 : Atm -> . PROVE Exp IN Exp END  / 12
7 : Atm -> PROVE . Exp IN Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 12
9 : Atm -> . BEGIN Exp END  / 12
10 : Atm -> . BACKTICK OExp  / 12
11 : Atm -> . REFINE IDENT  / 12
12 : Atm -> . LSQUARE Exps RSQUARE  / 12
13 : Atm -> . PUSH Names IN Exp END  / 12
14 : App -> . Atm  / 12
15 : App -> . App Atm  / 12
16 : Exp -> . App  / 4
17 : Exp -> . PRINT Atm  / 4
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 4

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 29
Atm => goto 17
App => goto 15

-----

State 9:

0 : Atm -> IDENT .  / 3

$ => reduce 0
LET => reduce 0
IN => reduce 0
LSQUARE => reduce 0
RSQUARE => reduce 0
LPAREN => reduce 0
RPAREN => reduce 0
COMMA => reduce 0
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

-----

State 10:

5 : Atm -> PROJ2 .  / 3

$ => reduce 5
LET => reduce 5
IN => reduce 5
LSQUARE => reduce 5
RSQUARE => reduce 5
LPAREN => reduce 5
RPAREN => reduce 5
COMMA => reduce 5
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

-----

State 11:

4 : Atm -> PROJ1 .  / 3

$ => reduce 4
LET => reduce 4
IN => reduce 4
LSQUARE => reduce 4
RSQUARE => reduce 4
LPAREN => reduce 4
RPAREN => reduce 4
COMMA => reduce 4
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

-----

State 12:

1 : Atm -> GOAL .  / 3

$ => reduce 1
LET => reduce 1
IN => reduce 1
LSQUARE => reduce 1
RSQUARE => reduce 1
LPAREN => reduce 1
RPAREN => reduce 1
COMMA => reduce 1
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

-----

State 13:

11 : Atm -> REFINE . IDENT  / 3

IDENT => shift 30

-----

State 14:

0 : Atm -> . IDENT  / 2
1 : Atm -> . GOAL  / 2
2 : Atm -> . LPAREN RPAREN  / 2
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 2
4 : Atm -> . PROJ1  / 2
5 : Atm -> . PROJ2  / 2
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 2
7 : Atm -> . PROVE Exp IN Exp END  / 2
8 : Atm -> . LPAREN Exp RPAREN  / 2
9 : Atm -> . BEGIN Exp END  / 2
10 : Atm -> . BACKTICK OExp  / 2
11 : Atm -> . REFINE IDENT  / 2
12 : Atm -> . LSQUARE Exps RSQUARE  / 2
13 : Atm -> . PUSH Names IN Exp END  / 2
17 : Exp -> PRINT . Atm  / 2

LET => shift 2
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
Atm => goto 31

-----

State 15:

0 : Atm -> . IDENT  / 3
1 : Atm -> . GOAL  / 3
2 : Atm -> . LPAREN RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 3
5 : Atm -> . PROJ2  / 3
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 3
7 : Atm -> . PROVE Exp IN Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 3
11 : Atm -> . REFINE IDENT  / 3
12 : Atm -> . LSQUARE Exps RSQUARE  / 3
13 : Atm -> . PUSH Names IN Exp END  / 3
15 : App -> App . Atm  / 3
16 : Exp -> App .  / 2

$ => reduce 16
LET => shift 2
IN => reduce 16
LSQUARE => shift 4
RSQUARE => reduce 16
LPAREN => shift 6
RPAREN => reduce 16
COMMA => reduce 16
BEGIN => shift 7
END => reduce 16
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
Atm => goto 32

-----

State 16:

start -> Exp .  / 0

$ => accept

-----

State 17:

14 : App -> Atm .  / 3

$ => reduce 14
LET => reduce 14
IN => reduce 14
LSQUARE => reduce 14
RSQUARE => reduce 14
LPAREN => reduce 14
RPAREN => reduce 14
COMMA => reduce 14
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

-----

State 18:

18 : Exp -> FN IDENT . DOUBLE_RIGHT_ARROW Exp  / 2

DOUBLE_RIGHT_ARROW => shift 33

-----

State 19:

6 : Atm -> LET IDENT . EQUALS Exp IN Exp END  / 3

EQUALS => shift 34

-----

State 20:

22 : Names -> IDENT . COMMA Names  / 4
23 : Names -> IDENT .  / 4

IN => reduce 23
COMMA => shift 35

-----

State 21:

13 : Atm -> PUSH Names . IN Exp END  / 3

IN => shift 36

-----

State 22:

19 : Exps -> Exp . COMMA Exps  / 7
20 : Exps -> Exp .  / 7

RSQUARE => reduce 20
COMMA => shift 37

-----

State 23:

12 : Atm -> LSQUARE Exps . RSQUARE  / 3

RSQUARE => shift 38

-----

State 24:

25 : OExp -> BOOL .  / 3

$ => reduce 25
LET => reduce 25
IN => reduce 25
LSQUARE => reduce 25
RSQUARE => reduce 25
LPAREN => reduce 25
RPAREN => reduce 25
COMMA => reduce 25
BEGIN => reduce 25
END => reduce 25
IDENT => reduce 25
PROVE => reduce 25
PROJ1 => reduce 25
PROJ2 => reduce 25
BACKTICK => reduce 25
REFINE => reduce 25
GOAL => reduce 25
PUSH => reduce 25

-----

State 25:

10 : Atm -> BACKTICK OExp .  / 3

$ => reduce 10
LET => reduce 10
IN => reduce 10
LSQUARE => reduce 10
RSQUARE => reduce 10
LPAREN => reduce 10
RPAREN => reduce 10
COMMA => reduce 10
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

-----

State 26:

2 : Atm -> LPAREN RPAREN .  / 3

$ => reduce 2
LET => reduce 2
IN => reduce 2
LSQUARE => reduce 2
RSQUARE => reduce 2
LPAREN => reduce 2
RPAREN => reduce 2
COMMA => reduce 2
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

-----

State 27:

3 : Atm -> LPAREN Exp . COMMA Exp RPAREN  / 3
8 : Atm -> LPAREN Exp . RPAREN  / 3

RPAREN => shift 39
COMMA => shift 40

-----

State 28:

9 : Atm -> BEGIN Exp . END  / 3

END => shift 41

-----

State 29:

7 : Atm -> PROVE Exp . IN Exp END  / 3

IN => shift 42

-----

State 30:

11 : Atm -> REFINE IDENT .  / 3

$ => reduce 11
LET => reduce 11
IN => reduce 11
LSQUARE => reduce 11
RSQUARE => reduce 11
LPAREN => reduce 11
RPAREN => reduce 11
COMMA => reduce 11
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

-----

State 31:

17 : Exp -> PRINT Atm .  / 2

$ => reduce 17
IN => reduce 17
RSQUARE => reduce 17
RPAREN => reduce 17
COMMA => reduce 17
END => reduce 17

-----

State 32:

15 : App -> App Atm .  / 3

$ => reduce 15
LET => reduce 15
IN => reduce 15
LSQUARE => reduce 15
RSQUARE => reduce 15
LPAREN => reduce 15
RPAREN => reduce 15
COMMA => reduce 15
BEGIN => reduce 15
END => reduce 15
IDENT => reduce 15
PROVE => reduce 15
PROJ1 => reduce 15
PROJ2 => reduce 15
BACKTICK => reduce 15
REFINE => reduce 15
GOAL => reduce 15
PUSH => reduce 15

-----

State 33:

0 : Atm -> . IDENT  / 3
1 : Atm -> . GOAL  / 3
2 : Atm -> . LPAREN RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 3
5 : Atm -> . PROJ2  / 3
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 3
7 : Atm -> . PROVE Exp IN Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 3
11 : Atm -> . REFINE IDENT  / 3
12 : Atm -> . LSQUARE Exps RSQUARE  / 3
13 : Atm -> . PUSH Names IN Exp END  / 3
14 : App -> . Atm  / 3
15 : App -> . App Atm  / 3
16 : Exp -> . App  / 2
17 : Exp -> . PRINT Atm  / 2
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 2
18 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW . Exp  / 2

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 43
Atm => goto 17
App => goto 15

-----

State 34:

0 : Atm -> . IDENT  / 12
1 : Atm -> . GOAL  / 12
2 : Atm -> . LPAREN RPAREN  / 12
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 12
4 : Atm -> . PROJ1  / 12
5 : Atm -> . PROJ2  / 12
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 12
6 : Atm -> LET IDENT EQUALS . Exp IN Exp END  / 3
7 : Atm -> . PROVE Exp IN Exp END  / 12
8 : Atm -> . LPAREN Exp RPAREN  / 12
9 : Atm -> . BEGIN Exp END  / 12
10 : Atm -> . BACKTICK OExp  / 12
11 : Atm -> . REFINE IDENT  / 12
12 : Atm -> . LSQUARE Exps RSQUARE  / 12
13 : Atm -> . PUSH Names IN Exp END  / 12
14 : App -> . Atm  / 12
15 : App -> . App Atm  / 12
16 : Exp -> . App  / 4
17 : Exp -> . PRINT Atm  / 4
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 4

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 44
Atm => goto 17
App => goto 15

-----

State 35:

22 : Names -> . IDENT COMMA Names  / 4
22 : Names -> IDENT COMMA . Names  / 4
23 : Names -> . IDENT  / 4
24 : Names -> .  / 4

IN => reduce 24
IDENT => shift 20
Names => goto 45

-----

State 36:

0 : Atm -> . IDENT  / 10
1 : Atm -> . GOAL  / 10
2 : Atm -> . LPAREN RPAREN  / 10
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 10
4 : Atm -> . PROJ1  / 10
5 : Atm -> . PROJ2  / 10
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 10
7 : Atm -> . PROVE Exp IN Exp END  / 10
8 : Atm -> . LPAREN Exp RPAREN  / 10
9 : Atm -> . BEGIN Exp END  / 10
10 : Atm -> . BACKTICK OExp  / 10
11 : Atm -> . REFINE IDENT  / 10
12 : Atm -> . LSQUARE Exps RSQUARE  / 10
13 : Atm -> . PUSH Names IN Exp END  / 10
13 : Atm -> PUSH Names IN . Exp END  / 3
14 : App -> . Atm  / 10
15 : App -> . App Atm  / 10
16 : Exp -> . App  / 11
17 : Exp -> . PRINT Atm  / 11
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 11

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 46
Atm => goto 17
App => goto 15

-----

State 37:

0 : Atm -> . IDENT  / 5
1 : Atm -> . GOAL  / 5
2 : Atm -> . LPAREN RPAREN  / 5
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 5
4 : Atm -> . PROJ1  / 5
5 : Atm -> . PROJ2  / 5
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 5
7 : Atm -> . PROVE Exp IN Exp END  / 5
8 : Atm -> . LPAREN Exp RPAREN  / 5
9 : Atm -> . BEGIN Exp END  / 5
10 : Atm -> . BACKTICK OExp  / 5
11 : Atm -> . REFINE IDENT  / 5
12 : Atm -> . LSQUARE Exps RSQUARE  / 5
13 : Atm -> . PUSH Names IN Exp END  / 5
14 : App -> . Atm  / 5
15 : App -> . App Atm  / 5
16 : Exp -> . App  / 6
17 : Exp -> . PRINT Atm  / 6
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 6
19 : Exps -> . Exp COMMA Exps  / 7
19 : Exps -> Exp COMMA . Exps  / 7
20 : Exps -> . Exp  / 7
21 : Exps -> .  / 7

LET => shift 2
FN => shift 1
LSQUARE => shift 4
RSQUARE => reduce 21
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 22
Atm => goto 17
Exps => goto 47
App => goto 15

-----

State 38:

12 : Atm -> LSQUARE Exps RSQUARE .  / 3

$ => reduce 12
LET => reduce 12
IN => reduce 12
LSQUARE => reduce 12
RSQUARE => reduce 12
LPAREN => reduce 12
RPAREN => reduce 12
COMMA => reduce 12
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

-----

State 39:

8 : Atm -> LPAREN Exp RPAREN .  / 3

$ => reduce 8
LET => reduce 8
IN => reduce 8
LSQUARE => reduce 8
RSQUARE => reduce 8
LPAREN => reduce 8
RPAREN => reduce 8
COMMA => reduce 8
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

-----

State 40:

0 : Atm -> . IDENT  / 13
1 : Atm -> . GOAL  / 13
2 : Atm -> . LPAREN RPAREN  / 13
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 13
3 : Atm -> LPAREN Exp COMMA . Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 13
5 : Atm -> . PROJ2  / 13
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 13
7 : Atm -> . PROVE Exp IN Exp END  / 13
8 : Atm -> . LPAREN Exp RPAREN  / 13
9 : Atm -> . BEGIN Exp END  / 13
10 : Atm -> . BACKTICK OExp  / 13
11 : Atm -> . REFINE IDENT  / 13
12 : Atm -> . LSQUARE Exps RSQUARE  / 13
13 : Atm -> . PUSH Names IN Exp END  / 13
14 : App -> . Atm  / 13
15 : App -> . App Atm  / 13
16 : Exp -> . App  / 14
17 : Exp -> . PRINT Atm  / 14
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 14

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 48
Atm => goto 17
App => goto 15

-----

State 41:

9 : Atm -> BEGIN Exp END .  / 3

$ => reduce 9
LET => reduce 9
IN => reduce 9
LSQUARE => reduce 9
RSQUARE => reduce 9
LPAREN => reduce 9
RPAREN => reduce 9
COMMA => reduce 9
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

-----

State 42:

0 : Atm -> . IDENT  / 10
1 : Atm -> . GOAL  / 10
2 : Atm -> . LPAREN RPAREN  / 10
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 10
4 : Atm -> . PROJ1  / 10
5 : Atm -> . PROJ2  / 10
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 10
7 : Atm -> . PROVE Exp IN Exp END  / 10
7 : Atm -> PROVE Exp IN . Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 10
9 : Atm -> . BEGIN Exp END  / 10
10 : Atm -> . BACKTICK OExp  / 10
11 : Atm -> . REFINE IDENT  / 10
12 : Atm -> . LSQUARE Exps RSQUARE  / 10
13 : Atm -> . PUSH Names IN Exp END  / 10
14 : App -> . Atm  / 10
15 : App -> . App Atm  / 10
16 : Exp -> . App  / 11
17 : Exp -> . PRINT Atm  / 11
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 11

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 49
Atm => goto 17
App => goto 15

-----

State 43:

18 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW Exp .  / 2

$ => reduce 18
IN => reduce 18
RSQUARE => reduce 18
RPAREN => reduce 18
COMMA => reduce 18
END => reduce 18

-----

State 44:

6 : Atm -> LET IDENT EQUALS Exp . IN Exp END  / 3

IN => shift 50

-----

State 45:

22 : Names -> IDENT COMMA Names .  / 4

IN => reduce 22

-----

State 46:

13 : Atm -> PUSH Names IN Exp . END  / 3

END => shift 51

-----

State 47:

19 : Exps -> Exp COMMA Exps .  / 7

RSQUARE => reduce 19

-----

State 48:

3 : Atm -> LPAREN Exp COMMA Exp . RPAREN  / 3

RPAREN => shift 52

-----

State 49:

7 : Atm -> PROVE Exp IN Exp . END  / 3

END => shift 53

-----

State 50:

0 : Atm -> . IDENT  / 10
1 : Atm -> . GOAL  / 10
2 : Atm -> . LPAREN RPAREN  / 10
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 10
4 : Atm -> . PROJ1  / 10
5 : Atm -> . PROJ2  / 10
6 : Atm -> . LET IDENT EQUALS Exp IN Exp END  / 10
6 : Atm -> LET IDENT EQUALS Exp IN . Exp END  / 3
7 : Atm -> . PROVE Exp IN Exp END  / 10
8 : Atm -> . LPAREN Exp RPAREN  / 10
9 : Atm -> . BEGIN Exp END  / 10
10 : Atm -> . BACKTICK OExp  / 10
11 : Atm -> . REFINE IDENT  / 10
12 : Atm -> . LSQUARE Exps RSQUARE  / 10
13 : Atm -> . PUSH Names IN Exp END  / 10
14 : App -> . Atm  / 10
15 : App -> . App Atm  / 10
16 : Exp -> . App  / 11
17 : Exp -> . PRINT Atm  / 11
18 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 11

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 6
BEGIN => shift 7
IDENT => shift 9
PROVE => shift 8
PROJ1 => shift 11
PROJ2 => shift 10
BACKTICK => shift 5
REFINE => shift 13
GOAL => shift 12
PUSH => shift 3
PRINT => shift 14
Exp => goto 54
Atm => goto 17
App => goto 15

-----

State 51:

13 : Atm -> PUSH Names IN Exp END .  / 3

$ => reduce 13
LET => reduce 13
IN => reduce 13
LSQUARE => reduce 13
RSQUARE => reduce 13
LPAREN => reduce 13
RPAREN => reduce 13
COMMA => reduce 13
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

-----

State 52:

3 : Atm -> LPAREN Exp COMMA Exp RPAREN .  / 3

$ => reduce 3
LET => reduce 3
IN => reduce 3
LSQUARE => reduce 3
RSQUARE => reduce 3
LPAREN => reduce 3
RPAREN => reduce 3
COMMA => reduce 3
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

-----

State 53:

7 : Atm -> PROVE Exp IN Exp END .  / 3

$ => reduce 7
LET => reduce 7
IN => reduce 7
LSQUARE => reduce 7
RSQUARE => reduce 7
LPAREN => reduce 7
RPAREN => reduce 7
COMMA => reduce 7
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

-----

State 54:

6 : Atm -> LET IDENT EQUALS Exp IN Exp . END  / 3

END => shift 55

-----

State 55:

6 : Atm -> LET IDENT EQUALS Exp IN Exp END .  / 3

$ => reduce 6
LET => reduce 6
IN => reduce 6
LSQUARE => reduce 6
RSQUARE => reduce 6
LPAREN => reduce 6
RPAREN => reduce 6
COMMA => reduce 6
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

-----

lookahead 0 = $ 
lookahead 1 = $ LET LSQUARE LPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 2 = $ IN RSQUARE RPAREN COMMA END 
lookahead 3 = $ LET IN LSQUARE RSQUARE LPAREN RPAREN COMMA BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 4 = IN 
lookahead 5 = LET LSQUARE RSQUARE LPAREN COMMA BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 6 = RSQUARE COMMA 
lookahead 7 = RSQUARE 
lookahead 8 = LET LSQUARE LPAREN RPAREN COMMA BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 9 = RPAREN COMMA 
lookahead 10 = LET LSQUARE LPAREN BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 11 = END 
lookahead 12 = LET IN LSQUARE LPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 13 = LET LSQUARE LPAREN RPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH 
lookahead 14 = RPAREN 

*)

struct
local
structure Value = struct
datatype nonterminal =
nonterminal
| pos of Arg.pos
| pos_string of Arg.pos_string
| exp of Arg.exp
| exps of Arg.exps
| names of Arg.names
| oexp of Arg.oexp
end
structure ParseEngine = ParseEngineFun (structure Streamable = Streamable
type terminal = Arg.terminal
type value = Value.nonterminal
val dummy = Value.nonterminal
fun read terminal =
(case terminal of
Arg.LET x => (1, Value.pos x)
| Arg.FN x => (2, Value.pos x)
| Arg.IN x => (3, Value.pos x)
| Arg.DOUBLE_RIGHT_ARROW x => (4, Value.pos x)
| Arg.LSQUARE x => (5, Value.pos x)
| Arg.RSQUARE x => (6, Value.pos x)
| Arg.LPAREN x => (7, Value.pos x)
| Arg.RPAREN x => (8, Value.pos x)
| Arg.COMMA x => (9, Value.pos x)
| Arg.EQUALS x => (10, Value.pos x)
| Arg.BEGIN x => (11, Value.pos x)
| Arg.END x => (12, Value.pos x)
| Arg.IDENT x => (13, Value.pos_string x)
| Arg.PROVE x => (14, Value.pos x)
| Arg.PROJ1 x => (15, Value.pos x)
| Arg.PROJ2 x => (16, Value.pos x)
| Arg.BACKTICK x => (17, Value.pos x)
| Arg.REFINE x => (18, Value.pos x)
| Arg.GOAL x => (19, Value.pos x)
| Arg.PUSH x => (20, Value.pos x)
| Arg.PRINT x => (21, Value.pos x)
| Arg.BOOL x => (22, Value.pos x)
)
)
in
val parse = ParseEngine.parse (
ParseEngine.next5x1 "\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\147\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128f\128\128\128\128\128\128\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133i\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\153\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\155\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128~~\128~\128~~~~~\128~~~~~~~~~~\128\128\128\128\128\128\128\128\128\128\128yy\128y\128yyyyy\128yyyyyyyyyy\128\128\128\128\128\128\128\128\128\128\128zz\128z\128zzzzz\128zzzzzzzzzz\128\128\128\128\128\128\128\128\128\128\128}}\128}\128}}}}}\128}}}}}}}}}}\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\159\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\128\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\128\128\128\128\128\128\128\128\128\128\128n\131\128n\128\133n\135nn\128\136n\138\137\140\139\134\142\141\132\128\128\128\128\128\128\128\128\128\128\128\127\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128pp\128p\128ppppp\128pppppppppp\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\162\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\163\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128g\128\128\128\128\128\164\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\165\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128j\128\128\166\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\167\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128ee\128e\128eeeee\128eeeeeeeeee\128\128\128\128\128\128\128\128\128\128\128tt\128t\128ttttt\128tttttttttt\128\128\128\128\128\128\128\128\128\128\128||\128|\128|||||\128||||||||||\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\168\169\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\170\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\171\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128ss\128s\128sssss\128ssssssssss\128\128\128\128\128\128\128\128\128\128\128m\128\128m\128\128m\128mm\128\128m\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128oo\128o\128ooooo\128oooooooooo\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\128\128f\128\128\128\128\128\128\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133i\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128rr\128r\128rrrrr\128rrrrrrrrrr\128\128\128\128\128\128\128\128\128\128\128vv\128v\128vvvvv\128vvvvvvvvvv\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128uu\128u\128uuuuu\128uuuuuuuuuu\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128l\128\128l\128\128l\128ll\128\128l\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\179\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128h\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\180\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128k\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\181\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\182\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\133\128\135\128\128\128\136\128\138\137\140\139\134\142\141\132\143\128\128\128\128\128\128\128\128\128\128qq\128q\128qqqqq\128qqqqqqqqqq\128\128\128\128\128\128\128\128\128\128\128{{\128{\128{{{{{\128{{{{{{{{{{\128\128\128\128\128\128\128\128\128\128\128ww\128w\128wwwww\128wwwwwwwwww\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\184\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128xx\128x\128xxxxx\128xxxxxxxxxx\128\128\128\128\128\128\128\128\128\128\128",
ParseEngine.next5x1 "\144\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\150\145\128\151\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\153\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\155\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\156\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\157\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\159\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\160\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\171\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\172\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\173\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\174\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\150\145\128\175\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\176\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\177\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\182\145\128\128\128\143\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
Vector.fromList [(1,1,(fn Value.pos_string(arg0)::rest => Value.exp(Arg.var arg0)::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.goal arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.pos(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.nil_ {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.pair {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.proj1 arg0)::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.proj2 arg0)::rest|_=>raise (Fail "bad parser"))),
(1,7,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::_::Value.pos_string(arg3)::Value.pos(arg4)::rest => Value.exp(Arg.let_ {5=arg0,4=arg1,3=arg2,2=arg3,1=arg4})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.prove {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn _::Value.exp(arg0)::_::rest => Value.exp(Arg.exp_atm arg0)::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn _::Value.exp(arg0)::_::rest => Value.exp(Arg.exp_atm arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.oexp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.quote {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.pos_string(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.refine {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn Value.pos(arg0)::Value.exps(arg1)::Value.pos(arg2)::rest => Value.exp(Arg.fork {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.names(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.push {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(5,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.atm_app arg0)::rest|_=>raise (Fail "bad parser"))),
(5,2,(fn Value.exp(arg0)::Value.exp(arg1)::rest => Value.exp(Arg.app {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(0,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.app_exp arg0)::rest|_=>raise (Fail "bad parser"))),
(0,2,(fn Value.exp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.print {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(0,4,(fn Value.exp(arg0)::_::Value.pos_string(arg1)::Value.pos(arg2)::rest => Value.exp(Arg.fn_ {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(3,3,(fn Value.exps(arg0)::_::Value.exp(arg1)::rest => Value.exps(Arg.exp_cons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(3,1,(fn Value.exp(arg0)::rest => Value.exps(Arg.exp_singl arg0)::rest|_=>raise (Fail "bad parser"))),
(3,0,(fn rest => Value.exps(Arg.exp_nil {})::rest)),
(4,3,(fn Value.names(arg0)::_::Value.pos_string(arg1)::rest => Value.names(Arg.names_cons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(4,1,(fn Value.pos_string(arg0)::rest => Value.names(Arg.names_singl arg0)::rest|_=>raise (Fail "bad parser"))),
(4,0,(fn rest => Value.names(Arg.names_nil {})::rest)),
(2,1,(fn Value.pos(arg0)::rest => Value.oexp(Arg.obool arg0)::rest|_=>raise (Fail "bad parser")))],
(fn Value.exp x => x | _ => raise (Fail "bad parser")), Arg.error)
end
end
