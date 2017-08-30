
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

          val off : pos -> oexp
          val ott : pos -> oexp
          val owbool : pos -> oexp
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
          val decl_nil : unit -> decls
          val decl_cons : decl * decls -> decls
          val declVal : pos_string * exp -> decl
          val push : pos * names * exp * pos -> exp
          val fork : pos * exps * pos -> exp
          val exact : pos * exp -> exp
          val refine : pos * pos_string -> exp
          val quote : pos * oexp -> exp
          val exp_atm : exp -> exp
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
           | BOOL of pos
           | WBOOL of pos
           | TT of pos
           | FF of pos
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
13 : Atm -> . LSQUARE Exps RSQUARE  / 1
14 : Atm -> . PUSH Names IN Exp END  / 1
18 : App -> . Atm  / 1
19 : App -> . App Atm  / 1
20 : Exp -> . App  / 0
21 : Exp -> . PRINT Atm  / 0
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 0

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 17
Atm => goto 15
App => goto 18

-----

State 1:

22 : Exp -> FN . IDENT DOUBLE_RIGHT_ARROW Exp  / 2

IDENT => shift 19

-----

State 2:

6 : Atm -> LET . Decls IN Exp END  / 3
15 : Decl -> . VAL IDENT EQUALS Exp  / 4
16 : Decls -> . Decl Decls  / 5
17 : Decls -> .  / 5

VAL => shift 22
IN => reduce 17
Decls => goto 21
Decl => goto 20

-----

State 3:

14 : Atm -> PUSH . Names IN Exp END  / 3
26 : Names -> . IDENT COMMA Names  / 5
27 : Names -> . IDENT  / 5
28 : Names -> .  / 5

IN => reduce 28
IDENT => shift 23
Names => goto 24

-----

State 4:

0 : Atm -> . IDENT  / 6
1 : Atm -> . GOAL  / 6
2 : Atm -> . LPAREN RPAREN  / 6
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 6
4 : Atm -> . PROJ1  / 6
5 : Atm -> . PROJ2  / 6
6 : Atm -> . LET Decls IN Exp END  / 6
7 : Atm -> . PROVE Exp BY Exp END  / 6
8 : Atm -> . LPAREN Exp RPAREN  / 6
9 : Atm -> . BEGIN Exp END  / 6
10 : Atm -> . BACKTICK OExp  / 6
11 : Atm -> . REFINE IDENT  / 6
12 : Atm -> . EXACT Atm  / 6
13 : Atm -> . LSQUARE Exps RSQUARE  / 6
13 : Atm -> LSQUARE . Exps RSQUARE  / 3
14 : Atm -> . PUSH Names IN Exp END  / 6
18 : App -> . Atm  / 6
19 : App -> . App Atm  / 6
20 : Exp -> . App  / 7
21 : Exp -> . PRINT Atm  / 7
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 7
23 : Exps -> . Exp COMMA Exps  / 8
24 : Exps -> . Exp  / 8
25 : Exps -> .  / 8

LET => shift 2
FN => shift 1
LSQUARE => shift 4
RSQUARE => reduce 25
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 25
Atm => goto 15
Exps => goto 26
App => goto 18

-----

State 5:

1 : Atm -> GOAL .  / 3

$ => reduce 1
LET => reduce 1
VAL => reduce 1
IN => reduce 1
BY => reduce 1
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
EXACT => reduce 1

-----

State 6:

10 : Atm -> BACKTICK . OExp  / 3
29 : OExp -> . BOOL  / 3
30 : OExp -> . WBOOL  / 3
31 : OExp -> . TT  / 3
32 : OExp -> . FF  / 3

BOOL => shift 30
WBOOL => shift 29
TT => shift 28
FF => shift 27
OExp => goto 31

-----

State 7:

0 : Atm -> . IDENT  / 9
1 : Atm -> . GOAL  / 9
2 : Atm -> . LPAREN RPAREN  / 9
2 : Atm -> LPAREN . RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 9
3 : Atm -> LPAREN . Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 9
5 : Atm -> . PROJ2  / 9
6 : Atm -> . LET Decls IN Exp END  / 9
7 : Atm -> . PROVE Exp BY Exp END  / 9
8 : Atm -> . LPAREN Exp RPAREN  / 9
8 : Atm -> LPAREN . Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 9
10 : Atm -> . BACKTICK OExp  / 9
11 : Atm -> . REFINE IDENT  / 9
12 : Atm -> . EXACT Atm  / 9
13 : Atm -> . LSQUARE Exps RSQUARE  / 9
14 : Atm -> . PUSH Names IN Exp END  / 9
18 : App -> . Atm  / 9
19 : App -> . App Atm  / 9
20 : Exp -> . App  / 10
21 : Exp -> . PRINT Atm  / 10
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 10

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
RPAREN => shift 32
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 33
Atm => goto 15
App => goto 18

-----

State 8:

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
9 : Atm -> BEGIN . Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . LSQUARE Exps RSQUARE  / 11
14 : Atm -> . PUSH Names IN Exp END  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : Exp -> . App  / 12
21 : Exp -> . PRINT Atm  / 12
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 34
Atm => goto 15
App => goto 18

-----

State 9:

0 : Atm -> . IDENT  / 13
1 : Atm -> . GOAL  / 13
2 : Atm -> . LPAREN RPAREN  / 13
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 13
4 : Atm -> . PROJ1  / 13
5 : Atm -> . PROJ2  / 13
6 : Atm -> . LET Decls IN Exp END  / 13
7 : Atm -> . PROVE Exp BY Exp END  / 13
7 : Atm -> PROVE . Exp BY Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 13
9 : Atm -> . BEGIN Exp END  / 13
10 : Atm -> . BACKTICK OExp  / 13
11 : Atm -> . REFINE IDENT  / 13
12 : Atm -> . EXACT Atm  / 13
13 : Atm -> . LSQUARE Exps RSQUARE  / 13
14 : Atm -> . PUSH Names IN Exp END  / 13
18 : App -> . Atm  / 13
19 : App -> . App Atm  / 13
20 : Exp -> . App  / 14
21 : Exp -> . PRINT Atm  / 14
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 14

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 35
Atm => goto 15
App => goto 18

-----

State 10:

0 : Atm -> IDENT .  / 3

$ => reduce 0
LET => reduce 0
VAL => reduce 0
IN => reduce 0
BY => reduce 0
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
EXACT => reduce 0

-----

State 11:

5 : Atm -> PROJ2 .  / 3

$ => reduce 5
LET => reduce 5
VAL => reduce 5
IN => reduce 5
BY => reduce 5
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
EXACT => reduce 5

-----

State 12:

4 : Atm -> PROJ1 .  / 3

$ => reduce 4
LET => reduce 4
VAL => reduce 4
IN => reduce 4
BY => reduce 4
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
EXACT => reduce 4

-----

State 13:

11 : Atm -> REFINE . IDENT  / 3

IDENT => shift 36

-----

State 14:

0 : Atm -> . IDENT  / 2
1 : Atm -> . GOAL  / 2
2 : Atm -> . LPAREN RPAREN  / 2
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 2
4 : Atm -> . PROJ1  / 2
5 : Atm -> . PROJ2  / 2
6 : Atm -> . LET Decls IN Exp END  / 2
7 : Atm -> . PROVE Exp BY Exp END  / 2
8 : Atm -> . LPAREN Exp RPAREN  / 2
9 : Atm -> . BEGIN Exp END  / 2
10 : Atm -> . BACKTICK OExp  / 2
11 : Atm -> . REFINE IDENT  / 2
12 : Atm -> . EXACT Atm  / 2
13 : Atm -> . LSQUARE Exps RSQUARE  / 2
14 : Atm -> . PUSH Names IN Exp END  / 2
21 : Exp -> PRINT . Atm  / 2

LET => shift 2
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
EXACT => shift 16
Atm => goto 37

-----

State 15:

18 : App -> Atm .  / 3

$ => reduce 18
LET => reduce 18
VAL => reduce 18
IN => reduce 18
BY => reduce 18
LSQUARE => reduce 18
RSQUARE => reduce 18
LPAREN => reduce 18
RPAREN => reduce 18
COMMA => reduce 18
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
EXACT => reduce 18

-----

State 16:

0 : Atm -> . IDENT  / 3
1 : Atm -> . GOAL  / 3
2 : Atm -> . LPAREN RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 3
5 : Atm -> . PROJ2  / 3
6 : Atm -> . LET Decls IN Exp END  / 3
7 : Atm -> . PROVE Exp BY Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 3
11 : Atm -> . REFINE IDENT  / 3
12 : Atm -> . EXACT Atm  / 3
12 : Atm -> EXACT . Atm  / 3
13 : Atm -> . LSQUARE Exps RSQUARE  / 3
14 : Atm -> . PUSH Names IN Exp END  / 3

LET => shift 2
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
EXACT => shift 16
Atm => goto 38

-----

State 17:

start -> Exp .  / 0

$ => accept

-----

State 18:

0 : Atm -> . IDENT  / 3
1 : Atm -> . GOAL  / 3
2 : Atm -> . LPAREN RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 3
5 : Atm -> . PROJ2  / 3
6 : Atm -> . LET Decls IN Exp END  / 3
7 : Atm -> . PROVE Exp BY Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 3
11 : Atm -> . REFINE IDENT  / 3
12 : Atm -> . EXACT Atm  / 3
13 : Atm -> . LSQUARE Exps RSQUARE  / 3
14 : Atm -> . PUSH Names IN Exp END  / 3
19 : App -> App . Atm  / 3
20 : Exp -> App .  / 2

$ => reduce 20
LET => shift 2
VAL => reduce 20
IN => reduce 20
BY => reduce 20
LSQUARE => shift 4
RSQUARE => reduce 20
LPAREN => shift 7
RPAREN => reduce 20
COMMA => reduce 20
BEGIN => shift 8
END => reduce 20
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
EXACT => shift 16
Atm => goto 39

-----

State 19:

22 : Exp -> FN IDENT . DOUBLE_RIGHT_ARROW Exp  / 2

DOUBLE_RIGHT_ARROW => shift 40

-----

State 20:

15 : Decl -> . VAL IDENT EQUALS Exp  / 4
16 : Decls -> . Decl Decls  / 5
16 : Decls -> Decl . Decls  / 5
17 : Decls -> .  / 5

VAL => shift 22
IN => reduce 17
Decls => goto 41
Decl => goto 20

-----

State 21:

6 : Atm -> LET Decls . IN Exp END  / 3

IN => shift 42

-----

State 22:

15 : Decl -> VAL . IDENT EQUALS Exp  / 4

IDENT => shift 43

-----

State 23:

26 : Names -> IDENT . COMMA Names  / 5
27 : Names -> IDENT .  / 5

IN => reduce 27
COMMA => shift 44

-----

State 24:

14 : Atm -> PUSH Names . IN Exp END  / 3

IN => shift 45

-----

State 25:

23 : Exps -> Exp . COMMA Exps  / 8
24 : Exps -> Exp .  / 8

RSQUARE => reduce 24
COMMA => shift 46

-----

State 26:

13 : Atm -> LSQUARE Exps . RSQUARE  / 3

RSQUARE => shift 47

-----

State 27:

32 : OExp -> FF .  / 3

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
EXACT => reduce 32

-----

State 28:

31 : OExp -> TT .  / 3

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
EXACT => reduce 31

-----

State 29:

30 : OExp -> WBOOL .  / 3

$ => reduce 30
LET => reduce 30
VAL => reduce 30
IN => reduce 30
BY => reduce 30
LSQUARE => reduce 30
RSQUARE => reduce 30
LPAREN => reduce 30
RPAREN => reduce 30
COMMA => reduce 30
BEGIN => reduce 30
END => reduce 30
IDENT => reduce 30
PROVE => reduce 30
PROJ1 => reduce 30
PROJ2 => reduce 30
BACKTICK => reduce 30
REFINE => reduce 30
GOAL => reduce 30
PUSH => reduce 30
EXACT => reduce 30

-----

State 30:

29 : OExp -> BOOL .  / 3

$ => reduce 29
LET => reduce 29
VAL => reduce 29
IN => reduce 29
BY => reduce 29
LSQUARE => reduce 29
RSQUARE => reduce 29
LPAREN => reduce 29
RPAREN => reduce 29
COMMA => reduce 29
BEGIN => reduce 29
END => reduce 29
IDENT => reduce 29
PROVE => reduce 29
PROJ1 => reduce 29
PROJ2 => reduce 29
BACKTICK => reduce 29
REFINE => reduce 29
GOAL => reduce 29
PUSH => reduce 29
EXACT => reduce 29

-----

State 31:

10 : Atm -> BACKTICK OExp .  / 3

$ => reduce 10
LET => reduce 10
VAL => reduce 10
IN => reduce 10
BY => reduce 10
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
EXACT => reduce 10

-----

State 32:

2 : Atm -> LPAREN RPAREN .  / 3

$ => reduce 2
LET => reduce 2
VAL => reduce 2
IN => reduce 2
BY => reduce 2
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
EXACT => reduce 2

-----

State 33:

3 : Atm -> LPAREN Exp . COMMA Exp RPAREN  / 3
8 : Atm -> LPAREN Exp . RPAREN  / 3

RPAREN => shift 48
COMMA => shift 49

-----

State 34:

9 : Atm -> BEGIN Exp . END  / 3

END => shift 50

-----

State 35:

7 : Atm -> PROVE Exp . BY Exp END  / 3

BY => shift 51

-----

State 36:

11 : Atm -> REFINE IDENT .  / 3

$ => reduce 11
LET => reduce 11
VAL => reduce 11
IN => reduce 11
BY => reduce 11
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
EXACT => reduce 11

-----

State 37:

21 : Exp -> PRINT Atm .  / 2

$ => reduce 21
VAL => reduce 21
IN => reduce 21
BY => reduce 21
RSQUARE => reduce 21
RPAREN => reduce 21
COMMA => reduce 21
END => reduce 21

-----

State 38:

12 : Atm -> EXACT Atm .  / 3

$ => reduce 12
LET => reduce 12
VAL => reduce 12
IN => reduce 12
BY => reduce 12
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
EXACT => reduce 12

-----

State 39:

19 : App -> App Atm .  / 3

$ => reduce 19
LET => reduce 19
VAL => reduce 19
IN => reduce 19
BY => reduce 19
LSQUARE => reduce 19
RSQUARE => reduce 19
LPAREN => reduce 19
RPAREN => reduce 19
COMMA => reduce 19
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
EXACT => reduce 19

-----

State 40:

0 : Atm -> . IDENT  / 3
1 : Atm -> . GOAL  / 3
2 : Atm -> . LPAREN RPAREN  / 3
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 3
5 : Atm -> . PROJ2  / 3
6 : Atm -> . LET Decls IN Exp END  / 3
7 : Atm -> . PROVE Exp BY Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 3
9 : Atm -> . BEGIN Exp END  / 3
10 : Atm -> . BACKTICK OExp  / 3
11 : Atm -> . REFINE IDENT  / 3
12 : Atm -> . EXACT Atm  / 3
13 : Atm -> . LSQUARE Exps RSQUARE  / 3
14 : Atm -> . PUSH Names IN Exp END  / 3
18 : App -> . Atm  / 3
19 : App -> . App Atm  / 3
20 : Exp -> . App  / 2
21 : Exp -> . PRINT Atm  / 2
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 2
22 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW . Exp  / 2

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 52
Atm => goto 15
App => goto 18

-----

State 41:

16 : Decls -> Decl Decls .  / 5

IN => reduce 16

-----

State 42:

0 : Atm -> . IDENT  / 11
1 : Atm -> . GOAL  / 11
2 : Atm -> . LPAREN RPAREN  / 11
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 11
4 : Atm -> . PROJ1  / 11
5 : Atm -> . PROJ2  / 11
6 : Atm -> . LET Decls IN Exp END  / 11
6 : Atm -> LET Decls IN . Exp END  / 3
7 : Atm -> . PROVE Exp BY Exp END  / 11
8 : Atm -> . LPAREN Exp RPAREN  / 11
9 : Atm -> . BEGIN Exp END  / 11
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . LSQUARE Exps RSQUARE  / 11
14 : Atm -> . PUSH Names IN Exp END  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : Exp -> . App  / 12
21 : Exp -> . PRINT Atm  / 12
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 53
Atm => goto 15
App => goto 18

-----

State 43:

15 : Decl -> VAL IDENT . EQUALS Exp  / 4

EQUALS => shift 54

-----

State 44:

26 : Names -> . IDENT COMMA Names  / 5
26 : Names -> IDENT COMMA . Names  / 5
27 : Names -> . IDENT  / 5
28 : Names -> .  / 5

IN => reduce 28
IDENT => shift 23
Names => goto 55

-----

State 45:

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
13 : Atm -> . LSQUARE Exps RSQUARE  / 11
14 : Atm -> . PUSH Names IN Exp END  / 11
14 : Atm -> PUSH Names IN . Exp END  / 3
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : Exp -> . App  / 12
21 : Exp -> . PRINT Atm  / 12
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 56
Atm => goto 15
App => goto 18

-----

State 46:

0 : Atm -> . IDENT  / 6
1 : Atm -> . GOAL  / 6
2 : Atm -> . LPAREN RPAREN  / 6
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 6
4 : Atm -> . PROJ1  / 6
5 : Atm -> . PROJ2  / 6
6 : Atm -> . LET Decls IN Exp END  / 6
7 : Atm -> . PROVE Exp BY Exp END  / 6
8 : Atm -> . LPAREN Exp RPAREN  / 6
9 : Atm -> . BEGIN Exp END  / 6
10 : Atm -> . BACKTICK OExp  / 6
11 : Atm -> . REFINE IDENT  / 6
12 : Atm -> . EXACT Atm  / 6
13 : Atm -> . LSQUARE Exps RSQUARE  / 6
14 : Atm -> . PUSH Names IN Exp END  / 6
18 : App -> . Atm  / 6
19 : App -> . App Atm  / 6
20 : Exp -> . App  / 7
21 : Exp -> . PRINT Atm  / 7
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 7
23 : Exps -> . Exp COMMA Exps  / 8
23 : Exps -> Exp COMMA . Exps  / 8
24 : Exps -> . Exp  / 8
25 : Exps -> .  / 8

LET => shift 2
FN => shift 1
LSQUARE => shift 4
RSQUARE => reduce 25
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 25
Atm => goto 15
Exps => goto 57
App => goto 18

-----

State 47:

13 : Atm -> LSQUARE Exps RSQUARE .  / 3

$ => reduce 13
LET => reduce 13
VAL => reduce 13
IN => reduce 13
BY => reduce 13
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
EXACT => reduce 13

-----

State 48:

8 : Atm -> LPAREN Exp RPAREN .  / 3

$ => reduce 8
LET => reduce 8
VAL => reduce 8
IN => reduce 8
BY => reduce 8
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
EXACT => reduce 8

-----

State 49:

0 : Atm -> . IDENT  / 15
1 : Atm -> . GOAL  / 15
2 : Atm -> . LPAREN RPAREN  / 15
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 15
3 : Atm -> LPAREN Exp COMMA . Exp RPAREN  / 3
4 : Atm -> . PROJ1  / 15
5 : Atm -> . PROJ2  / 15
6 : Atm -> . LET Decls IN Exp END  / 15
7 : Atm -> . PROVE Exp BY Exp END  / 15
8 : Atm -> . LPAREN Exp RPAREN  / 15
9 : Atm -> . BEGIN Exp END  / 15
10 : Atm -> . BACKTICK OExp  / 15
11 : Atm -> . REFINE IDENT  / 15
12 : Atm -> . EXACT Atm  / 15
13 : Atm -> . LSQUARE Exps RSQUARE  / 15
14 : Atm -> . PUSH Names IN Exp END  / 15
18 : App -> . Atm  / 15
19 : App -> . App Atm  / 15
20 : Exp -> . App  / 16
21 : Exp -> . PRINT Atm  / 16
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 16

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 58
Atm => goto 15
App => goto 18

-----

State 50:

9 : Atm -> BEGIN Exp END .  / 3

$ => reduce 9
LET => reduce 9
VAL => reduce 9
IN => reduce 9
BY => reduce 9
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
EXACT => reduce 9

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
7 : Atm -> PROVE Exp BY . Exp END  / 3
8 : Atm -> . LPAREN Exp RPAREN  / 11
9 : Atm -> . BEGIN Exp END  / 11
10 : Atm -> . BACKTICK OExp  / 11
11 : Atm -> . REFINE IDENT  / 11
12 : Atm -> . EXACT Atm  / 11
13 : Atm -> . LSQUARE Exps RSQUARE  / 11
14 : Atm -> . PUSH Names IN Exp END  / 11
18 : App -> . Atm  / 11
19 : App -> . App Atm  / 11
20 : Exp -> . App  / 12
21 : Exp -> . PRINT Atm  / 12
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 59
Atm => goto 15
App => goto 18

-----

State 52:

22 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW Exp .  / 2

$ => reduce 22
VAL => reduce 22
IN => reduce 22
BY => reduce 22
RSQUARE => reduce 22
RPAREN => reduce 22
COMMA => reduce 22
END => reduce 22

-----

State 53:

6 : Atm -> LET Decls IN Exp . END  / 3

END => shift 60

-----

State 54:

0 : Atm -> . IDENT  / 17
1 : Atm -> . GOAL  / 17
2 : Atm -> . LPAREN RPAREN  / 17
3 : Atm -> . LPAREN Exp COMMA Exp RPAREN  / 17
4 : Atm -> . PROJ1  / 17
5 : Atm -> . PROJ2  / 17
6 : Atm -> . LET Decls IN Exp END  / 17
7 : Atm -> . PROVE Exp BY Exp END  / 17
8 : Atm -> . LPAREN Exp RPAREN  / 17
9 : Atm -> . BEGIN Exp END  / 17
10 : Atm -> . BACKTICK OExp  / 17
11 : Atm -> . REFINE IDENT  / 17
12 : Atm -> . EXACT Atm  / 17
13 : Atm -> . LSQUARE Exps RSQUARE  / 17
14 : Atm -> . PUSH Names IN Exp END  / 17
15 : Decl -> VAL IDENT EQUALS . Exp  / 4
18 : App -> . Atm  / 17
19 : App -> . App Atm  / 17
20 : Exp -> . App  / 4
21 : Exp -> . PRINT Atm  / 4
22 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 4

LET => shift 2
FN => shift 1
LSQUARE => shift 4
LPAREN => shift 7
BEGIN => shift 8
IDENT => shift 10
PROVE => shift 9
PROJ1 => shift 12
PROJ2 => shift 11
BACKTICK => shift 6
REFINE => shift 13
GOAL => shift 5
PUSH => shift 3
PRINT => shift 14
EXACT => shift 16
Exp => goto 61
Atm => goto 15
App => goto 18

-----

State 55:

26 : Names -> IDENT COMMA Names .  / 5

IN => reduce 26

-----

State 56:

14 : Atm -> PUSH Names IN Exp . END  / 3

END => shift 62

-----

State 57:

23 : Exps -> Exp COMMA Exps .  / 8

RSQUARE => reduce 23

-----

State 58:

3 : Atm -> LPAREN Exp COMMA Exp . RPAREN  / 3

RPAREN => shift 63

-----

State 59:

7 : Atm -> PROVE Exp BY Exp . END  / 3

END => shift 64

-----

State 60:

6 : Atm -> LET Decls IN Exp END .  / 3

$ => reduce 6
LET => reduce 6
VAL => reduce 6
IN => reduce 6
BY => reduce 6
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
EXACT => reduce 6

-----

State 61:

15 : Decl -> VAL IDENT EQUALS Exp .  / 4

VAL => reduce 15
IN => reduce 15

-----

State 62:

14 : Atm -> PUSH Names IN Exp END .  / 3

$ => reduce 14
LET => reduce 14
VAL => reduce 14
IN => reduce 14
BY => reduce 14
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
EXACT => reduce 14

-----

State 63:

3 : Atm -> LPAREN Exp COMMA Exp RPAREN .  / 3

$ => reduce 3
LET => reduce 3
VAL => reduce 3
IN => reduce 3
BY => reduce 3
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
EXACT => reduce 3

-----

State 64:

7 : Atm -> PROVE Exp BY Exp END .  / 3

$ => reduce 7
LET => reduce 7
VAL => reduce 7
IN => reduce 7
BY => reduce 7
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
EXACT => reduce 7

-----

lookahead 0 = $ 
lookahead 1 = $ LET LSQUARE LPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 2 = $ VAL IN BY RSQUARE RPAREN COMMA END 
lookahead 3 = $ LET VAL IN BY LSQUARE RSQUARE LPAREN RPAREN COMMA BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 4 = VAL IN 
lookahead 5 = IN 
lookahead 6 = LET LSQUARE RSQUARE LPAREN COMMA BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 7 = RSQUARE COMMA 
lookahead 8 = RSQUARE 
lookahead 9 = LET LSQUARE LPAREN RPAREN COMMA BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 10 = RPAREN COMMA 
lookahead 11 = LET LSQUARE LPAREN BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 12 = END 
lookahead 13 = LET BY LSQUARE LPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 14 = BY 
lookahead 15 = LET LSQUARE LPAREN RPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 
lookahead 16 = RPAREN 
lookahead 17 = LET VAL IN LSQUARE LPAREN BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH EXACT 

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
| Arg.BOOL x => (25, Value.pos x)
| Arg.WBOOL x => (26, Value.pos x)
| Arg.TT x => (27, Value.pos x)
| Arg.FF x => (28, Value.pos x)
| Arg.EXACT x => (29, Value.pos x)
)
)
in
val parse = ParseEngine.parse (
ParseEngine.next5x1 "\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151m\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128b\128\128\128\128\128\128\128\128\128\128\128\152\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\133e\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128}}\128}}}\128}}}}}\128\128}}}}}}}}}}\128\128\128\128\128}\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\159\158\157\156\128\128\128\128\131\130\128\128\128\128\133\128\136\161\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128~~\128~~~\128~~~~~\128\128~~~~~~~~~~\128\128\128\128\128~\128\128yy\128yyy\128yyyyy\128\128yyyyyyyyyy\128\128\128\128\128y\128\128zz\128zzz\128zzzzz\128\128zzzzzzzzzz\128\128\128\128\128z\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\165\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\128\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\128\128\128\128\128\145\128\128ll\128lll\128lllll\128\128llllllllll\128\128\128\128\128l\128\128\128\131\128\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\128\128\128\128\128\145\128\128\127\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128j\131\128jjj\128\133j\136jj\128\128\137j\139\138\141\140\135\142\134\132\128\128\128\128\128\145\128\128\128\128\128\128\128\128\169\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\151m\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\171\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\172\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128c\128\128\128\128\128\128\173\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\174\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128f\128\128\175\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\176\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128^^\128^^^\128^^^^^\128\128^^^^^^^^^^\128\128\128\128\128^\128\128__\128___\128_____\128\128__________\128\128\128\128\128_\128\128``\128```\128`````\128\128``````````\128\128\128\128\128`\128\128aa\128aaa\128aaaaa\128\128aaaaaaaaaa\128\128\128\128\128a\128\128tt\128ttt\128ttttt\128\128tttttttttt\128\128\128\128\128t\128\128||\128|||\128|||||\128\128||||||||||\128\128\128\128\128|\128\128\128\128\128\128\128\128\128\128\128\128\177\178\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\179\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\180\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128ss\128sss\128sssss\128\128ssssssssss\128\128\128\128\128s\128\128i\128\128iii\128\128i\128ii\128\128\128i\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128rr\128rrr\128rrrrr\128\128rrrrrrrrrr\128\128\128\128\128r\128\128kk\128kkk\128kkkkk\128\128kkkkkkkkkk\128\128\128\128\128k\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\128\128\128n\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\183\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128b\128\128\128\128\128\128\128\128\128\128\128\152\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\131\130\128\128\128\128\133e\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128qq\128qqq\128qqqqq\128\128qqqqqqqqqq\128\128\128\128\128q\128\128vv\128vvv\128vvvvv\128\128vvvvvvvvvv\128\128\128\128\128v\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128uu\128uuu\128uuuuu\128\128uuuuuuuuuu\128\128\128\128\128u\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128h\128\128hhh\128\128h\128hh\128\128\128h\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\189\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\133\128\136\128\128\128\128\137\128\139\138\141\140\135\142\134\132\143\128\128\128\128\145\128\128\128\128\128\128d\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\191\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128g\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\192\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\193\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128xx\128xxx\128xxxxx\128\128xxxxxxxxxx\128\128\128\128\128x\128\128\128\128\128oo\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128pp\128ppp\128ppppp\128\128pppppppppp\128\128\128\128\128p\128\128{{\128{{{\128{{{{{\128\128{{{{{{{{{{\128\128\128\128\128{\128\128ww\128www\128wwwww\128\128wwwwwwwwww\128\128\128\128\128w\128\128",
ParseEngine.next5x1 "\145\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\149\128\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\152\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\153\143\128\128\154\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\159\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\161\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\162\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\163\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\165\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\166\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\167\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\169\128\128\128\148\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\180\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\181\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\183\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\184\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\153\143\128\128\185\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\186\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\187\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\189\143\128\128\128\128\128\146\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
Vector.fromList [(1,1,(fn Value.pos_string(arg0)::rest => Value.exp(Arg.var arg0)::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.goal arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.pos(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.nil_ {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.pair {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.proj1 arg0)::rest|_=>raise (Fail "bad parser"))),
(1,1,(fn Value.pos(arg0)::rest => Value.exp(Arg.proj2 arg0)::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.decls(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.let_ {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.exp(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.prove {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn _::Value.exp(arg0)::_::rest => Value.exp(Arg.exp_atm arg0)::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn _::Value.exp(arg0)::_::rest => Value.exp(Arg.exp_atm arg0)::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.oexp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.quote {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.pos_string(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.refine {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,2,(fn Value.exp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.exact {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(1,3,(fn Value.pos(arg0)::Value.exps(arg1)::Value.pos(arg2)::rest => Value.exp(Arg.fork {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(1,5,(fn Value.pos(arg0)::Value.exp(arg1)::_::Value.names(arg2)::Value.pos(arg3)::rest => Value.exp(Arg.push {4=arg0,3=arg1,2=arg2,1=arg3})::rest|_=>raise (Fail "bad parser"))),
(6,4,(fn Value.exp(arg0)::_::Value.pos_string(arg1)::_::rest => Value.decl(Arg.declVal {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(2,2,(fn Value.decls(arg0)::Value.decl(arg1)::rest => Value.decls(Arg.decl_cons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(2,0,(fn rest => Value.decls(Arg.decl_nil {})::rest)),
(7,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.atm_app arg0)::rest|_=>raise (Fail "bad parser"))),
(7,2,(fn Value.exp(arg0)::Value.exp(arg1)::rest => Value.exp(Arg.app {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(0,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.app_exp arg0)::rest|_=>raise (Fail "bad parser"))),
(0,2,(fn Value.exp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.print {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(0,4,(fn Value.exp(arg0)::_::Value.pos_string(arg1)::Value.pos(arg2)::rest => Value.exp(Arg.fn_ {3=arg0,2=arg1,1=arg2})::rest|_=>raise (Fail "bad parser"))),
(4,3,(fn Value.exps(arg0)::_::Value.exp(arg1)::rest => Value.exps(Arg.exp_cons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(4,1,(fn Value.exp(arg0)::rest => Value.exps(Arg.exp_singl arg0)::rest|_=>raise (Fail "bad parser"))),
(4,0,(fn rest => Value.exps(Arg.exp_nil {})::rest)),
(5,3,(fn Value.names(arg0)::_::Value.pos_string(arg1)::rest => Value.names(Arg.names_cons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(5,1,(fn Value.pos_string(arg0)::rest => Value.names(Arg.names_singl arg0)::rest|_=>raise (Fail "bad parser"))),
(5,0,(fn rest => Value.names(Arg.names_nil {})::rest)),
(3,1,(fn Value.pos(arg0)::rest => Value.oexp(Arg.obool arg0)::rest|_=>raise (Fail "bad parser"))),
(3,1,(fn Value.pos(arg0)::rest => Value.oexp(Arg.owbool arg0)::rest|_=>raise (Fail "bad parser"))),
(3,1,(fn Value.pos(arg0)::rest => Value.oexp(Arg.ott arg0)::rest|_=>raise (Fail "bad parser"))),
(3,1,(fn Value.pos(arg0)::rest => Value.oexp(Arg.off arg0)::rest|_=>raise (Fail "bad parser")))],
(fn Value.exp x => x | _ => raise (Fail "bad parser")), Arg.error)
end
end
