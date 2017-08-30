
functor MetalanguageLexFn
   (structure Streamable : STREAMABLE
    structure Arg :
       sig
          type symbol
          val ord : symbol -> int

          type t

          type self = { lexmain : symbol Streamable.t -> t }
          type info = { match : symbol list,
                        len : int,
                        start : symbol Streamable.t,
                        follow : symbol Streamable.t,
                        self : self }

          val backtick : info -> t
          val bool : info -> t
          val by : info -> t
          val comma : info -> t
          val double_right_arrow : info -> t
          val end_ : info -> t
          val eof : info -> t
          val equals : info -> t
          val error : info -> t
          val exact : info -> t
          val ff : info -> t
          val fn_ : info -> t
          val goal : info -> t
          val ident : info -> t
          val in_ : info -> t
          val let_ : info -> t
          val lparen : info -> t
          val lsquare : info -> t
          val print : info -> t
          val proj1 : info -> t
          val proj2 : info -> t
          val prove : info -> t
          val refine : info -> t
          val rparen : info -> t
          val rsquare : info -> t
          val skip : info -> t
          val tt : info -> t
          val val_ : info -> t
          val wbool : info -> t
       end)
   :>
   sig
      val lexmain : Arg.symbol Streamable.t -> Arg.t
   end
=

(*

AUTOMATON LISTINGS
==================

Automaton lexmain
initial state = 43
total states = 67

-----

lexmain state 12 (final:bool):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 13 (final:goal):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 14 (final:let_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 15 (final:val_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 16 (final:skip):

9-10 => state 16   (final:skip)
13 => state 16   (final:skip)
32 => state 16   (final:skip)

-----

lexmain state 17 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-107 => state 25   (final:ident)
108 => state 37   (final:wbool)
109-122 => state 25   (final:ident)

-----

lexmain state 18 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 20   (final:ident)
111-122 => state 25   (final:ident)

-----

lexmain state 19 (final:refine):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 20 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 19   (final:refine)
102-122 => state 25   (final:ident)

-----

lexmain state 21 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 56   (final:in_)
111-122 => state 25   (final:ident)

-----

lexmain state 22 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 40   (final:print)
117-122 => state 25   (final:ident)

-----

lexmain state 23 (final:fn_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 24 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-117 => state 25   (final:ident)
118 => state 29   (final:ident)
119-122 => state 25   (final:ident)

-----

lexmain state 25 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 26 (final:prove):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 27 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97 => state 49   (final:ident)
98-122 => state 25   (final:ident)

-----

lexmain state 28 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97 => state 55   (final:ident)
98-122 => state 25   (final:ident)

-----

lexmain state 29 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 26   (final:prove)
102-122 => state 25   (final:ident)

-----

lexmain state 30 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 34   (final:exact)
117-122 => state 25   (final:ident)

-----

lexmain state 31 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 42   (final:ident)
111-119 => state 25   (final:ident)
120 => state 28   (final:ident)
121-122 => state 25   (final:ident)

-----

lexmain state 32 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 50   (final:tt)
117-122 => state 25   (final:ident)

-----

lexmain state 33 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 22   (final:ident)
111-122 => state 25   (final:ident)

-----

lexmain state 34 (final:exact):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 35 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 36 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-107 => state 25   (final:ident)
108 => state 12   (final:bool)
109-122 => state 25   (final:ident)

-----

lexmain state 37 (final:wbool):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 38 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 17   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 39 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 48   (final:ident)
102-122 => state 25   (final:ident)

-----

lexmain state 40 (final:print):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 41 (final:end_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 42 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-99 => state 25   (final:ident)
100 => state 41   (final:end_)
101-122 => state 25   (final:ident)

-----

lexmain state 43 (initial, final:error):

0-8 => state 5   (sink:error)
9-10 => state 47   (final:skip)
11-12 => state 5   (sink:error)
13 => state 47   (final:skip)
14-31 => state 5   (sink:error)
32 => state 47   (final:skip)
33-34 => state 5   (sink:error)
35 => state 57   (final:error)
36-39 => state 5   (sink:error)
40 => state 3   (sink:lparen)
41 => state 8   (sink:rparen)
42-43 => state 5   (sink:error)
44 => state 10   (sink:comma)
45 => state 35   (final:ident)
46 => state 5   (sink:error)
47 => state 35   (final:ident)
48-60 => state 5   (sink:error)
61 => state 44   (final:equals)
62-64 => state 5   (sink:error)
65-90 => state 35   (final:ident)
91 => state 4   (sink:lsquare)
92 => state 35   (final:ident)
93 => state 1   (sink:rsquare)
94 => state 5   (sink:error)
95 => state 35   (final:ident)
96 => state 9   (sink:backtick)
97 => state 35   (final:ident)
98 => state 66   (final:ident)
99-100 => state 35   (final:ident)
101 => state 31   (final:ident)
102 => state 60   (final:ident)
103 => state 59   (final:ident)
104 => state 35   (final:ident)
105 => state 21   (final:ident)
106-107 => state 35   (final:ident)
108 => state 54   (final:ident)
109-111 => state 35   (final:ident)
112 => state 62   (final:ident)
113 => state 35   (final:ident)
114 => state 39   (final:ident)
115 => state 35   (final:ident)
116 => state 32   (final:ident)
117 => state 35   (final:ident)
118 => state 27   (final:ident)
119 => state 46   (final:ident)
120-122 => state 35   (final:ident)
123-127 => state 5   (sink:error)
EOS => state 11   (sink:eof)

-----

lexmain state 44 (final:equals):

62 => state 7   (sink:double_right_arrow)

-----

lexmain state 45 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-104 => state 25   (final:ident)
105 => state 33   (final:ident)
106-110 => state 25   (final:ident)
111 => state 24   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 46 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97 => state 25   (final:ident)
98 => state 63   (final:ident)
99-122 => state 25   (final:ident)

-----

lexmain state 47 (final:skip):

9-10 => state 16   (final:skip)
13 => state 16   (final:skip)
32 => state 16   (final:skip)

-----

lexmain state 48 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-101 => state 25   (final:ident)
102 => state 61   (final:ident)
103-122 => state 25   (final:ident)

-----

lexmain state 49 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-107 => state 25   (final:ident)
108 => state 15   (final:val_)
109-122 => state 25   (final:ident)

-----

lexmain state 50 (final:tt):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 51 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 36   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 52 (final:ff):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 53 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 14   (final:let_)
117-122 => state 25   (final:ident)

-----

lexmain state 54 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 53   (final:ident)
102-122 => state 25   (final:ident)

-----

lexmain state 55 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-98 => state 25   (final:ident)
99 => state 30   (final:ident)
100-122 => state 25   (final:ident)

-----

lexmain state 56 (final:in_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 57 (final:error):

49 => state 2   (sink:proj1)
50 => state 6   (sink:proj2)

-----

lexmain state 58 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97 => state 64   (final:ident)
98-122 => state 25   (final:ident)

-----

lexmain state 59 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 58   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 60 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-101 => state 25   (final:ident)
102 => state 52   (final:ff)
103-109 => state 25   (final:ident)
110 => state 23   (final:fn_)
111-122 => state 25   (final:ident)

-----

lexmain state 61 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-104 => state 25   (final:ident)
105 => state 18   (final:ident)
106-122 => state 25   (final:ident)

-----

lexmain state 62 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-113 => state 25   (final:ident)
114 => state 45   (final:ident)
115-122 => state 25   (final:ident)

-----

lexmain state 63 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 38   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 64 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-107 => state 25   (final:ident)
108 => state 13   (final:goal)
109-122 => state 25   (final:ident)

-----

lexmain state 65 (final:by):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 66 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 51   (final:ident)
112-120 => state 25   (final:ident)
121 => state 65   (final:by)
122 => state 25   (final:ident)

*)

struct
local
structure LexEngine = LexEngineFun (structure Streamable = Streamable
type symbol = Arg.symbol
val ord = Arg.ord)
structure Tables = struct
fun epsilon _ = raise (Fail "Illegal lexeme")
val lexmain = (43, 11, 66, Vector.fromList [Arg.rsquare,Arg.proj1,Arg.lparen,Arg.lsquare,Arg.error,Arg.proj2,Arg.double_right_arrow,Arg.rparen,Arg.backtick,Arg.comma,Arg.eof,Arg.bool,Arg.goal,Arg.let_,Arg.val_,Arg.skip,Arg.ident,Arg.ident,Arg.refine,Arg.ident,Arg.ident,Arg.ident,Arg.fn_,Arg.ident,Arg.ident,Arg.prove,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.exact,Arg.ident,Arg.ident,Arg.wbool,Arg.ident,Arg.ident,Arg.print,Arg.end_,Arg.ident,Arg.error,Arg.equals,Arg.ident,Arg.ident,Arg.skip,Arg.ident,Arg.ident,Arg.tt,Arg.ident,Arg.ff,Arg.ident,Arg.ident,Arg.ident,Arg.in_,Arg.error,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.by,Arg.ident], LexEngine.next7x1 128 "\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^P\^P\^@\^@\^P\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^P\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y%\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^T\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^S\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y8\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y(\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^]\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@1\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@7\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Z\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\"\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y*\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^\\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y2\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^V\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\f\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Q\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y0\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y)\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^E\^E\^E\^E\^E\^E\^E\^E\^E//\^E\^E/\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E/\^E\^E9\^E\^E\^E\^E\^C\b\^E\^E\n#\^E#\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E\^E,\^E\^E\^E##########################\^D#\^A\^E#\t#B##\^_<;#\^U##6###>#'# #\^[.###\^E\^E\^E\^E\^E\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\a\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y!\^Y\^Y\^Y\^Y\^Y\^X\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y?\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^P\^P\^@\^@\^P\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^P\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y=\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^O\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y$\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^N\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y5\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^^\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^B\^F\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y:\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y4\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^W\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^R\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y-\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y&\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\r\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y3\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^YA\^Y\^@\^@\^@\^@\^@", LexEngine.next0x1 "\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\v\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@")
end
in
fun lexmain s = LexEngine.lex {lexmain=lexmain} Tables.lexmain s
end
end
