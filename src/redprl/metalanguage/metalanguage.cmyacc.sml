
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
          val seqExpExp : exp -> exp
          val seqExpCons : exp * exp -> exp
          val app_exp : exp -> exp
          val app : exp * exp -> exp
          val atm_app : exp -> exp
          val decl_nil : unit -> decls
          val decl_cons : decl * decls -> decls
          val declVal : pos_string * exp -> decl
          val print : pos * exp -> exp
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
15 : Atm -> . PRINT Atm  / 1
19 : App -> . Atm  / 1
20 : App -> . App Atm  / 1
21 : SeqExp -> . App  / 0
22 : SeqExp -> . App SEMI SeqExp  / 0
23 : Exp -> . SeqExp  / 0
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 0

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 18
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 1:

24 : Exp -> FN . IDENT DOUBLE_RIGHT_ARROW Exp  / 2

IDENT => shift 20

-----

State 2:

6 : Atm -> LET . Decls IN Exp END  / 3
16 : Decl -> . VAL IDENT EQUALS Exp  / 4
17 : Decls -> . Decl Decls  / 5
18 : Decls -> .  / 5

VAL => shift 23
IN => reduce 18
Decls => goto 22
Decl => goto 21

-----

State 3:

23 : Exp -> SeqExp .  / 2

$ => reduce 23
VAL => reduce 23
IN => reduce 23
BY => reduce 23
RSQUARE => reduce 23
RPAREN => reduce 23
COMMA => reduce 23
END => reduce 23

-----

State 4:

19 : App -> Atm .  / 3

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

State 5:

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
15 : Atm -> . PRINT Atm  / 3

LET => shift 2
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Atm => goto 24

-----

State 6:

14 : Atm -> PUSH . Names IN Exp END  / 3
28 : Names -> . IDENT COMMA Names  / 5
29 : Names -> . IDENT  / 5
30 : Names -> .  / 5

IN => reduce 30
IDENT => shift 25
Names => goto 26

-----

State 7:

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
15 : Atm -> . PRINT Atm  / 6
19 : App -> . Atm  / 6
20 : App -> . App Atm  / 6
21 : SeqExp -> . App  / 7
22 : SeqExp -> . App SEMI SeqExp  / 7
23 : Exp -> . SeqExp  / 7
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 7
25 : Exps -> . Exp COMMA Exps  / 8
26 : Exps -> . Exp  / 8
27 : Exps -> .  / 8

LET => shift 2
FN => shift 1
LSQUARE => shift 7
RSQUARE => reduce 27
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 27
Atm => goto 4
Exps => goto 28
App => goto 19
SeqExp => goto 3

-----

State 8:

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

State 9:

10 : Atm -> BACKTICK . OExp  / 3
31 : OExp -> . BOOL  / 3
32 : OExp -> . WBOOL  / 3
33 : OExp -> . TT  / 3
34 : OExp -> . FF  / 3

BOOL => shift 32
WBOOL => shift 31
TT => shift 30
FF => shift 29
OExp => goto 33

-----

State 10:

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
15 : Atm -> . PRINT Atm  / 9
19 : App -> . Atm  / 9
20 : App -> . App Atm  / 9
21 : SeqExp -> . App  / 10
22 : SeqExp -> . App SEMI SeqExp  / 10
23 : Exp -> . SeqExp  / 10
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 10

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
RPAREN => shift 34
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 35
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 11:

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
15 : Atm -> . PRINT Atm  / 11
19 : App -> . Atm  / 11
20 : App -> . App Atm  / 11
21 : SeqExp -> . App  / 12
22 : SeqExp -> . App SEMI SeqExp  / 12
23 : Exp -> . SeqExp  / 12
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 36
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 12:

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
15 : Atm -> . PRINT Atm  / 13
19 : App -> . Atm  / 13
20 : App -> . App Atm  / 13
21 : SeqExp -> . App  / 14
22 : SeqExp -> . App SEMI SeqExp  / 14
23 : Exp -> . SeqExp  / 14
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 14

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 37
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 13:

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

State 14:

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

State 15:

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

State 16:

11 : Atm -> REFINE . IDENT  / 3

IDENT => shift 38

-----

State 17:

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
15 : Atm -> . PRINT Atm  / 3
15 : Atm -> PRINT . Atm  / 3

LET => shift 2
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Atm => goto 39

-----

State 18:

start -> Exp .  / 0

$ => accept

-----

State 19:

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
15 : Atm -> . PRINT Atm  / 3
20 : App -> App . Atm  / 3
21 : SeqExp -> App .  / 2
22 : SeqExp -> App . SEMI SeqExp  / 2

$ => reduce 21
LET => shift 2
VAL => reduce 21
IN => reduce 21
BY => reduce 21
LSQUARE => shift 7
RSQUARE => reduce 21
LPAREN => shift 10
RPAREN => reduce 21
COMMA => reduce 21
SEMI => shift 40
BEGIN => shift 11
END => reduce 21
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Atm => goto 41

-----

State 20:

24 : Exp -> FN IDENT . DOUBLE_RIGHT_ARROW Exp  / 2

DOUBLE_RIGHT_ARROW => shift 42

-----

State 21:

16 : Decl -> . VAL IDENT EQUALS Exp  / 4
17 : Decls -> . Decl Decls  / 5
17 : Decls -> Decl . Decls  / 5
18 : Decls -> .  / 5

VAL => shift 23
IN => reduce 18
Decls => goto 43
Decl => goto 21

-----

State 22:

6 : Atm -> LET Decls . IN Exp END  / 3

IN => shift 44

-----

State 23:

16 : Decl -> VAL . IDENT EQUALS Exp  / 4

IDENT => shift 45

-----

State 24:

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

State 25:

28 : Names -> IDENT . COMMA Names  / 5
29 : Names -> IDENT .  / 5

IN => reduce 29
COMMA => shift 46

-----

State 26:

14 : Atm -> PUSH Names . IN Exp END  / 3

IN => shift 47

-----

State 27:

25 : Exps -> Exp . COMMA Exps  / 8
26 : Exps -> Exp .  / 8

RSQUARE => reduce 26
COMMA => shift 48

-----

State 28:

13 : Atm -> LSQUARE Exps . RSQUARE  / 3

RSQUARE => shift 49

-----

State 29:

34 : OExp -> FF .  / 3

$ => reduce 34
LET => reduce 34
VAL => reduce 34
IN => reduce 34
BY => reduce 34
LSQUARE => reduce 34
RSQUARE => reduce 34
LPAREN => reduce 34
RPAREN => reduce 34
COMMA => reduce 34
SEMI => reduce 34
BEGIN => reduce 34
END => reduce 34
IDENT => reduce 34
PROVE => reduce 34
PROJ1 => reduce 34
PROJ2 => reduce 34
BACKTICK => reduce 34
REFINE => reduce 34
GOAL => reduce 34
PUSH => reduce 34
PRINT => reduce 34
EXACT => reduce 34

-----

State 30:

33 : OExp -> TT .  / 3

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

State 31:

32 : OExp -> WBOOL .  / 3

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

State 32:

31 : OExp -> BOOL .  / 3

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

State 33:

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

State 34:

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

State 35:

3 : Atm -> LPAREN Exp . COMMA Exp RPAREN  / 3
8 : Atm -> LPAREN Exp . RPAREN  / 3

RPAREN => shift 50
COMMA => shift 51

-----

State 36:

9 : Atm -> BEGIN Exp . END  / 3

END => shift 52

-----

State 37:

7 : Atm -> PROVE Exp . BY Exp END  / 3

BY => shift 53

-----

State 38:

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

State 39:

15 : Atm -> PRINT Atm .  / 3

$ => reduce 15
LET => reduce 15
VAL => reduce 15
IN => reduce 15
BY => reduce 15
LSQUARE => reduce 15
RSQUARE => reduce 15
LPAREN => reduce 15
RPAREN => reduce 15
COMMA => reduce 15
SEMI => reduce 15
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
PRINT => reduce 15
EXACT => reduce 15

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
15 : Atm -> . PRINT Atm  / 3
19 : App -> . Atm  / 3
20 : App -> . App Atm  / 3
21 : SeqExp -> . App  / 2
22 : SeqExp -> . App SEMI SeqExp  / 2
22 : SeqExp -> App SEMI . SeqExp  / 2

LET => shift 2
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Atm => goto 4
App => goto 19
SeqExp => goto 54

-----

State 41:

20 : App -> App Atm .  / 3

$ => reduce 20
LET => reduce 20
VAL => reduce 20
IN => reduce 20
BY => reduce 20
LSQUARE => reduce 20
RSQUARE => reduce 20
LPAREN => reduce 20
RPAREN => reduce 20
COMMA => reduce 20
SEMI => reduce 20
BEGIN => reduce 20
END => reduce 20
IDENT => reduce 20
PROVE => reduce 20
PROJ1 => reduce 20
PROJ2 => reduce 20
BACKTICK => reduce 20
REFINE => reduce 20
GOAL => reduce 20
PUSH => reduce 20
PRINT => reduce 20
EXACT => reduce 20

-----

State 42:

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
15 : Atm -> . PRINT Atm  / 3
19 : App -> . Atm  / 3
20 : App -> . App Atm  / 3
21 : SeqExp -> . App  / 2
22 : SeqExp -> . App SEMI SeqExp  / 2
23 : Exp -> . SeqExp  / 2
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 2
24 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW . Exp  / 2

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 55
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 43:

17 : Decls -> Decl Decls .  / 5

IN => reduce 17

-----

State 44:

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
15 : Atm -> . PRINT Atm  / 11
19 : App -> . Atm  / 11
20 : App -> . App Atm  / 11
21 : SeqExp -> . App  / 12
22 : SeqExp -> . App SEMI SeqExp  / 12
23 : Exp -> . SeqExp  / 12
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 56
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 45:

16 : Decl -> VAL IDENT . EQUALS Exp  / 4

EQUALS => shift 57

-----

State 46:

28 : Names -> . IDENT COMMA Names  / 5
28 : Names -> IDENT COMMA . Names  / 5
29 : Names -> . IDENT  / 5
30 : Names -> .  / 5

IN => reduce 30
IDENT => shift 25
Names => goto 58

-----

State 47:

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
15 : Atm -> . PRINT Atm  / 11
19 : App -> . Atm  / 11
20 : App -> . App Atm  / 11
21 : SeqExp -> . App  / 12
22 : SeqExp -> . App SEMI SeqExp  / 12
23 : Exp -> . SeqExp  / 12
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 59
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 48:

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
15 : Atm -> . PRINT Atm  / 6
19 : App -> . Atm  / 6
20 : App -> . App Atm  / 6
21 : SeqExp -> . App  / 7
22 : SeqExp -> . App SEMI SeqExp  / 7
23 : Exp -> . SeqExp  / 7
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 7
25 : Exps -> . Exp COMMA Exps  / 8
25 : Exps -> Exp COMMA . Exps  / 8
26 : Exps -> . Exp  / 8
27 : Exps -> .  / 8

LET => shift 2
FN => shift 1
LSQUARE => shift 7
RSQUARE => reduce 27
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 27
Atm => goto 4
Exps => goto 60
App => goto 19
SeqExp => goto 3

-----

State 49:

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

State 50:

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

State 51:

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
15 : Atm -> . PRINT Atm  / 15
19 : App -> . Atm  / 15
20 : App -> . App Atm  / 15
21 : SeqExp -> . App  / 16
22 : SeqExp -> . App SEMI SeqExp  / 16
23 : Exp -> . SeqExp  / 16
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 16

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 61
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 52:

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

State 53:

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
15 : Atm -> . PRINT Atm  / 11
19 : App -> . Atm  / 11
20 : App -> . App Atm  / 11
21 : SeqExp -> . App  / 12
22 : SeqExp -> . App SEMI SeqExp  / 12
23 : Exp -> . SeqExp  / 12
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 12

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 62
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 54:

22 : SeqExp -> App SEMI SeqExp .  / 2

$ => reduce 22
VAL => reduce 22
IN => reduce 22
BY => reduce 22
RSQUARE => reduce 22
RPAREN => reduce 22
COMMA => reduce 22
END => reduce 22

-----

State 55:

24 : Exp -> FN IDENT DOUBLE_RIGHT_ARROW Exp .  / 2

$ => reduce 24
VAL => reduce 24
IN => reduce 24
BY => reduce 24
RSQUARE => reduce 24
RPAREN => reduce 24
COMMA => reduce 24
END => reduce 24

-----

State 56:

6 : Atm -> LET Decls IN Exp . END  / 3

END => shift 63

-----

State 57:

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
15 : Atm -> . PRINT Atm  / 17
16 : Decl -> VAL IDENT EQUALS . Exp  / 4
19 : App -> . Atm  / 17
20 : App -> . App Atm  / 17
21 : SeqExp -> . App  / 4
22 : SeqExp -> . App SEMI SeqExp  / 4
23 : Exp -> . SeqExp  / 4
24 : Exp -> . FN IDENT DOUBLE_RIGHT_ARROW Exp  / 4

LET => shift 2
FN => shift 1
LSQUARE => shift 7
LPAREN => shift 10
BEGIN => shift 11
IDENT => shift 13
PROVE => shift 12
PROJ1 => shift 15
PROJ2 => shift 14
BACKTICK => shift 9
REFINE => shift 16
GOAL => shift 8
PUSH => shift 6
PRINT => shift 17
EXACT => shift 5
Exp => goto 64
Atm => goto 4
App => goto 19
SeqExp => goto 3

-----

State 58:

28 : Names -> IDENT COMMA Names .  / 5

IN => reduce 28

-----

State 59:

14 : Atm -> PUSH Names IN Exp . END  / 3

END => shift 65

-----

State 60:

25 : Exps -> Exp COMMA Exps .  / 8

RSQUARE => reduce 25

-----

State 61:

3 : Atm -> LPAREN Exp COMMA Exp . RPAREN  / 3

RPAREN => shift 66

-----

State 62:

7 : Atm -> PROVE Exp BY Exp . END  / 3

END => shift 67

-----

State 63:

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

State 64:

16 : Decl -> VAL IDENT EQUALS Exp .  / 4

VAL => reduce 16
IN => reduce 16

-----

State 65:

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

State 66:

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

State 67:

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

lookahead 0 = $ 
lookahead 1 = $ LET LSQUARE LPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 2 = $ VAL IN BY RSQUARE RPAREN COMMA END 
lookahead 3 = $ LET VAL IN BY LSQUARE RSQUARE LPAREN RPAREN COMMA SEMI BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 4 = VAL IN 
lookahead 5 = IN 
lookahead 6 = LET LSQUARE RSQUARE LPAREN COMMA SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 7 = RSQUARE COMMA 
lookahead 8 = RSQUARE 
lookahead 9 = LET LSQUARE LPAREN RPAREN COMMA SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 10 = RPAREN COMMA 
lookahead 11 = LET LSQUARE LPAREN SEMI BEGIN END IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 12 = END 
lookahead 13 = LET BY LSQUARE LPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 14 = BY 
lookahead 15 = LET LSQUARE LPAREN RPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 
lookahead 16 = RPAREN 
lookahead 17 = LET VAL IN LSQUARE LPAREN SEMI BEGIN IDENT PROVE PROJ1 PROJ2 BACKTICK REFINE GOAL PUSH PRINT EXACT 

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
ParseEngine.next5x1 "\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\152l\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128g\128\128ggg\128\128g\128gg\128\128\128g\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128kk\128kkk\128kkkkkk\128kkkkkkkkkkk\128\128\128\128k\128\128\128\131\128\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\128\128\128`\128\128\128\128\128\128\128\128\128\128\128\154\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\136c\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128}}\128}}}\128}}}}}}\128}}}}}}}}}}}\128\128\128\128}\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\161\160\159\158\128\128\128\128\131\130\128\128\128\128\136\128\139\163\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128~~\128~~~\128~~~~~~\128~~~~~~~~~~~\128\128\128\128~\128\128yy\128yyy\128yyyyyy\128yyyyyyyyyyy\128\128\128\128y\128\128zz\128zzz\128zzzzzz\128zzzzzzzzzzz\128\128\128\128z\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\167\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\128\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\127\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128i\131\128iii\128\136i\139ii\169\128\140i\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\128\128\128\128\128\171\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\152l\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\173\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\174\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128rr\128rrr\128rrrrrr\128rrrrrrrrrrr\128\128\128\128r\128\128\128\128\128\128a\128\128\128\128\128\128\175\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\176\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128d\128\128\177\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\178\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\\\\\128\\\\\\\128\\\\\\\\\\\\\128\\\\\\\\\\\\\\\\\\\\\\\128\128\128\128\\\128\128]]\128]]]\128]]]]]]\128]]]]]]]]]]]\128\128\128\128]\128\128^^\128^^^\128^^^^^^\128^^^^^^^^^^^\128\128\128\128^\128\128__\128___\128______\128___________\128\128\128\128_\128\128tt\128ttt\128tttttt\128ttttttttttt\128\128\128\128t\128\128||\128|||\128||||||\128|||||||||||\128\128\128\128|\128\128\128\128\128\128\128\128\128\128\128\128\179\180\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\181\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\182\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128ss\128sss\128ssssss\128sssssssssss\128\128\128\128s\128\128oo\128ooo\128oooooo\128ooooooooooo\128\128\128\128o\128\128\128\131\128\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128jj\128jjj\128jjjjjj\128jjjjjjjjjjj\128\128\128\128j\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\128\128\128m\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\186\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128`\128\128\128\128\128\128\128\128\128\128\128\154\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\131\130\128\128\128\128\136c\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128qq\128qqq\128qqqqqq\128qqqqqqqqqqq\128\128\128\128q\128\128vv\128vvv\128vvvvvv\128vvvvvvvvvvv\128\128\128\128v\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128uu\128uuu\128uuuuuu\128uuuuuuuuuuu\128\128\128\128u\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128h\128\128hhh\128\128h\128hh\128\128\128h\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128f\128\128fff\128\128f\128ff\128\128\128f\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\192\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\131\130\128\128\128\128\136\128\139\128\128\128\128\140\128\142\141\144\143\138\145\137\135\146\128\128\128\128\134\128\128\128\128\128\128b\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\194\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128e\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\195\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\196\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128xx\128xxx\128xxxxxx\128xxxxxxxxxxx\128\128\128\128x\128\128\128\128\128nn\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128pp\128ppp\128pppppp\128ppppppppppp\128\128\128\128p\128\128{{\128{{{\128{{{{{{\128{{{{{{{{{{{\128\128\128\128{\128\128ww\128www\128wwwwww\128wwwwwwwwwww\128\128\128\128w\128\128",
ParseEngine.next5x1 "\146\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\150\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\152\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\154\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\155\132\128\128\156\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\161\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\163\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\164\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\165\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\167\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\169\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\171\128\128\128\149\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\132\128\128\128\128\128\147\182\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\183\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\184\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\186\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\187\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\155\132\128\128\188\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\189\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\190\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\192\132\128\128\128\128\128\147\131\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128\128",
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
(1,2,(fn Value.exp(arg0)::Value.pos(arg1)::rest => Value.exp(Arg.print {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(6,4,(fn Value.exp(arg0)::_::Value.pos_string(arg1)::_::rest => Value.decl(Arg.declVal {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(2,2,(fn Value.decls(arg0)::Value.decl(arg1)::rest => Value.decls(Arg.decl_cons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(2,0,(fn rest => Value.decls(Arg.decl_nil {})::rest)),
(7,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.atm_app arg0)::rest|_=>raise (Fail "bad parser"))),
(7,2,(fn Value.exp(arg0)::Value.exp(arg1)::rest => Value.exp(Arg.app {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(8,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.app_exp arg0)::rest|_=>raise (Fail "bad parser"))),
(8,3,(fn Value.exp(arg0)::_::Value.exp(arg1)::rest => Value.exp(Arg.seqExpCons {2=arg0,1=arg1})::rest|_=>raise (Fail "bad parser"))),
(0,1,(fn Value.exp(arg0)::rest => Value.exp(Arg.seqExpExp arg0)::rest|_=>raise (Fail "bad parser"))),
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
