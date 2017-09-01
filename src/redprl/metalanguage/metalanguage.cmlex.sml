
functor MetalanguageLexFn
   (structure Streamable : STREAMABLE
    structure Arg :
       sig
          type symbol
          val ord : symbol -> int

          type t

          type self = { lexMain : symbol Streamable.t -> t }
          type info = { match : symbol list,
                        len : int,
                        start : symbol Streamable.t,
                        follow : symbol Streamable.t,
                        self : self }

          val backtick : info -> t
          val begin : info -> t
          val by : info -> t
          val colon : info -> t
          val comma : info -> t
          val dim : info -> t
          val double_right_arrow : info -> t
          val end_ : info -> t
          val eof : info -> t
          val equals : info -> t
          val error : info -> t
          val exact : info -> t
          val exp : info -> t
          val fn_ : info -> t
          val goal : info -> t
          val ident : info -> t
          val in_ : info -> t
          val lbrace : info -> t
          val let_ : info -> t
          val lparen : info -> t
          val lsquare : info -> t
          val print : info -> t
          val proj1 : info -> t
          val proj2 : info -> t
          val prove : info -> t
          val push : info -> t
          val rbrace : info -> t
          val refine : info -> t
          val rparen : info -> t
          val rsquare : info -> t
          val semi : info -> t
          val skip : info -> t
          val val_ : info -> t
       end)
   :>
   sig
      val lexMain : Arg.symbol Streamable.t -> Arg.t
   end
=

(*

AUTOMATON LISTINGS
==================

Automaton lexMain
initial state = 73
total states = 75

-----

lexMain state 16 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-104 => state 55   (final:ident)
105 => state 51   (final:ident)
106-122 => state 55   (final:ident)

-----

lexMain state 17 (final:skip):

0-9 => state 17   (final:skip)
11-127 => state 17   (final:skip)

-----

lexMain state 18 (final:ident):

0-9 => state 17   (final:skip)
11-38 => state 17   (final:skip)
39 => state 31   (final:skip)
40-44 => state 17   (final:skip)
45 => state 31   (final:skip)
46 => state 17   (final:skip)
47-57 => state 31   (final:skip)
58-64 => state 17   (final:skip)
65-90 => state 31   (final:skip)
91 => state 17   (final:skip)
92 => state 31   (final:skip)
93-94 => state 17   (final:skip)
95 => state 31   (final:skip)
96 => state 17   (final:skip)
97-122 => state 31   (final:skip)
123-127 => state 17   (final:skip)

-----

lexMain state 19 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-108 => state 55   (final:ident)
109 => state 47   (final:dim)
110-122 => state 55   (final:ident)

-----

lexMain state 20 (final:fn_):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 21 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-104 => state 55   (final:ident)
105 => state 66   (final:ident)
106-122 => state 55   (final:ident)

-----

lexMain state 22 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-109 => state 55   (final:ident)
110 => state 39   (final:in_)
111-122 => state 55   (final:ident)

-----

lexMain state 23 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-107 => state 55   (final:ident)
108 => state 60   (final:goal)
109-122 => state 55   (final:ident)

-----

lexMain state 24 (final:val_):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 25 (final:exact):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 26 (final:push):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 27 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-115 => state 55   (final:ident)
116 => state 38   (final:print)
117-122 => state 55   (final:ident)

-----

lexMain state 28 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-101 => state 55   (final:ident)
102 => state 21   (final:ident)
103-122 => state 55   (final:ident)

-----

lexMain state 29 (final:skip):

9-10 => state 33   (final:skip)
13 => state 33   (final:skip)
32 => state 33   (final:skip)

-----

lexMain state 30 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-100 => state 55   (final:ident)
101 => state 63   (final:refine)
102-122 => state 55   (final:ident)

-----

lexMain state 31 (final:skip):

0-9 => state 17   (final:skip)
11-38 => state 17   (final:skip)
39 => state 31   (final:skip)
40-44 => state 17   (final:skip)
45 => state 31   (final:skip)
46 => state 17   (final:skip)
47-57 => state 31   (final:skip)
58-64 => state 17   (final:skip)
65-90 => state 31   (final:skip)
91 => state 17   (final:skip)
92 => state 31   (final:skip)
93-94 => state 17   (final:skip)
95 => state 31   (final:skip)
96 => state 17   (final:skip)
97-122 => state 31   (final:skip)
123-127 => state 17   (final:skip)

-----

lexMain state 32 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-104 => state 55   (final:ident)
105 => state 19   (final:ident)
106-122 => state 55   (final:ident)

-----

lexMain state 33 (final:skip):

9-10 => state 33   (final:skip)
13 => state 33   (final:skip)
32 => state 33   (final:skip)

-----

lexMain state 34 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-100 => state 55   (final:ident)
101 => state 28   (final:ident)
102-122 => state 55   (final:ident)

-----

lexMain state 35 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-117 => state 55   (final:ident)
118 => state 48   (final:ident)
119-122 => state 55   (final:ident)

-----

lexMain state 36 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-109 => state 55   (final:ident)
110 => state 49   (final:ident)
111-119 => state 55   (final:ident)
120 => state 62   (final:ident)
121-122 => state 55   (final:ident)

-----

lexMain state 37 (final:prove):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 38 (final:print):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 39 (final:in_):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 40 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-100 => state 55   (final:ident)
101 => state 72   (final:ident)
102-122 => state 55   (final:ident)

-----

lexMain state 41 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-109 => state 55   (final:ident)
110 => state 27   (final:ident)
111-122 => state 55   (final:ident)

-----

lexMain state 42 (final:by):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 43 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-110 => state 55   (final:ident)
111 => state 54   (final:ident)
112-122 => state 55   (final:ident)

-----

lexMain state 44 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-113 => state 55   (final:ident)
114 => state 67   (final:ident)
115-116 => state 55   (final:ident)
117 => state 71   (final:ident)
118-122 => state 55   (final:ident)

-----

lexMain state 45 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-107 => state 55   (final:ident)
108 => state 24   (final:val_)
109-122 => state 55   (final:ident)

-----

lexMain state 46 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 47 (final:dim):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 48 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-100 => state 55   (final:ident)
101 => state 37   (final:prove)
102-122 => state 55   (final:ident)

-----

lexMain state 49 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-99 => state 55   (final:ident)
100 => state 59   (final:end_)
101-122 => state 55   (final:ident)

-----

lexMain state 50 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97 => state 45   (final:ident)
98-122 => state 55   (final:ident)

-----

lexMain state 51 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-109 => state 55   (final:ident)
110 => state 52   (final:begin)
111-122 => state 55   (final:ident)

-----

lexMain state 52 (final:begin):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 53 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-109 => state 55   (final:ident)
110 => state 20   (final:fn_)
111-122 => state 55   (final:ident)

-----

lexMain state 54 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97 => state 23   (final:ident)
98-122 => state 55   (final:ident)

-----

lexMain state 55 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 56 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-115 => state 55   (final:ident)
116 => state 25   (final:exact)
117-122 => state 55   (final:ident)

-----

lexMain state 57 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-98 => state 55   (final:ident)
99 => state 56   (final:ident)
100-122 => state 55   (final:ident)

-----

lexMain state 58 (final:exp):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 59 (final:end_):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 60 (final:goal):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 61 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-100 => state 55   (final:ident)
101 => state 65   (final:ident)
102-120 => state 55   (final:ident)
121 => state 42   (final:by)
122 => state 55   (final:ident)

-----

lexMain state 62 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97 => state 57   (final:ident)
98-111 => state 55   (final:ident)
112 => state 58   (final:exp)
113-122 => state 55   (final:ident)

-----

lexMain state 63 (final:refine):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 64 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47 => state 18   (final:ident)
48-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

-----

lexMain state 65 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-102 => state 55   (final:ident)
103 => state 16   (final:ident)
104-122 => state 55   (final:ident)

-----

lexMain state 66 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-109 => state 55   (final:ident)
110 => state 30   (final:ident)
111-122 => state 55   (final:ident)

-----

lexMain state 67 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-104 => state 55   (final:ident)
105 => state 41   (final:ident)
106-110 => state 55   (final:ident)
111 => state 35   (final:ident)
112-122 => state 55   (final:ident)

-----

lexMain state 68 (final:equals):

62 => state 3   (sink:double_right_arrow)

-----

lexMain state 69 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-103 => state 55   (final:ident)
104 => state 26   (final:push)
105-122 => state 55   (final:ident)

-----

lexMain state 70 (final:error):

49 => state 1   (sink:proj1)
50 => state 12   (sink:proj2)

-----

lexMain state 71 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-114 => state 55   (final:ident)
115 => state 69   (final:ident)
116-122 => state 55   (final:ident)

-----

lexMain state 72 (final:ident):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-115 => state 55   (final:ident)
116 => state 74   (final:let_)
117-122 => state 55   (final:ident)

-----

lexMain state 73 (initial, final:error):

0-8 => state 14   (sink:error)
9-10 => state 29   (final:skip)
11-12 => state 14   (sink:error)
13 => state 29   (final:skip)
14-31 => state 14   (sink:error)
32 => state 29   (final:skip)
33-34 => state 14   (sink:error)
35 => state 70   (final:error)
36-39 => state 14   (sink:error)
40 => state 10   (sink:lparen)
41 => state 4   (sink:rparen)
42-43 => state 14   (sink:error)
44 => state 2   (sink:comma)
45 => state 46   (final:ident)
46 => state 14   (sink:error)
47 => state 64   (final:ident)
48-57 => state 14   (sink:error)
58 => state 11   (sink:colon)
59 => state 9   (sink:semi)
60 => state 14   (sink:error)
61 => state 68   (final:equals)
62-64 => state 14   (sink:error)
65-90 => state 46   (final:ident)
91 => state 13   (sink:lsquare)
92 => state 46   (final:ident)
93 => state 7   (sink:rsquare)
94 => state 14   (sink:error)
95 => state 46   (final:ident)
96 => state 8   (sink:backtick)
97 => state 46   (final:ident)
98 => state 61   (final:ident)
99 => state 46   (final:ident)
100 => state 32   (final:ident)
101 => state 36   (final:ident)
102 => state 53   (final:ident)
103 => state 43   (final:ident)
104 => state 46   (final:ident)
105 => state 22   (final:ident)
106-107 => state 46   (final:ident)
108 => state 40   (final:ident)
109-111 => state 46   (final:ident)
112 => state 44   (final:ident)
113 => state 46   (final:ident)
114 => state 34   (final:ident)
115-117 => state 46   (final:ident)
118 => state 50   (final:ident)
119-122 => state 46   (final:ident)
123 => state 5   (sink:lbrace)
124 => state 14   (sink:error)
125 => state 6   (sink:rbrace)
126-127 => state 14   (sink:error)
EOS => state 15   (sink:eof)

-----

lexMain state 74 (final:let_):

39 => state 55   (final:ident)
45 => state 55   (final:ident)
47-57 => state 55   (final:ident)
65-90 => state 55   (final:ident)
92 => state 55   (final:ident)
95 => state 55   (final:ident)
97-122 => state 55   (final:ident)

*)

struct
local
structure LexEngine = LexEngineFun (structure Streamable = Streamable
type symbol = Arg.symbol
val ord = Arg.ord)
structure Tables = struct
fun epsilon _ = raise (Fail "Illegal lexeme")
val lexMain = (73, 15, 74, Vector.fromList [Arg.proj1,Arg.comma,Arg.double_right_arrow,Arg.rparen,Arg.lbrace,Arg.rbrace,Arg.rsquare,Arg.backtick,Arg.semi,Arg.lparen,Arg.colon,Arg.proj2,Arg.lsquare,Arg.error,Arg.eof,Arg.ident,Arg.skip,Arg.ident,Arg.ident,Arg.fn_,Arg.ident,Arg.ident,Arg.ident,Arg.val_,Arg.exact,Arg.push,Arg.ident,Arg.ident,Arg.skip,Arg.ident,Arg.skip,Arg.ident,Arg.skip,Arg.ident,Arg.ident,Arg.ident,Arg.prove,Arg.print,Arg.in_,Arg.ident,Arg.ident,Arg.by,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.dim,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.begin,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.exp,Arg.end_,Arg.goal,Arg.ident,Arg.ident,Arg.refine,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.equals,Arg.ident,Arg.error,Arg.ident,Arg.ident,Arg.error,Arg.let_], LexEngine.next7x1 128 "\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777377777777777777777\^@\^@\^@\^@\^@\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^@\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^@\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^_\^Q\^Q\^Q\^Q\^Q\^_\^Q\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^Q\^_\^Q\^Q\^_\^Q\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^Q\^Q\^Q\^Q\^Q\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@777777777777/7777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777B77777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777'777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777<77777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777777777&777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777\^U77777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@!!\^@\^@!\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@!\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777?777777777777777777777\^@\^@\^@\^@\^@\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^@\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^_\^Q\^Q\^Q\^Q\^Q\^_\^Q\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^Q\^Q\^Q\^Q\^Q\^Q\^Q\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^Q\^_\^Q\^Q\^_\^Q\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^_\^Q\^Q\^Q\^Q\^Q\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777\^S77777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@!!\^@\^@!\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@!\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777\^\777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777707777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777771777777777>77\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777H777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777\^[777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777677777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777C77G77777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777\^X77777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777%777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@777;7777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@-7777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777774777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777\^T777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@\^W7777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777777777\^Y777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77877777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777A7777777777777777777*7\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@977777777777777:7777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@\^R7777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@777777\^P7777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777\^^777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777)77777#77777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^C\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777\^Z777777777777777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^A\f\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@777777777777777777E7777777\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@7777777777777777777J777777\^@\^@\^@\^@\^@\^N\^N\^N\^N\^N\^N\^N\^N\^N\^]\^]\^N\^N\^]\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\^]\^N\^NF\^N\^N\^N\^N\n\^D\^N\^N\^B.\^N@\^N\^N\^N\^N\^N\^N\^N\^N\^N\^N\v\t\^ND\^N\^N\^N..........................\r.\a\^N.\b.=. $5+.\^V..(...,.\"...2....\^E\^N\^F\^N\^N\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@7\^@\^@\^@\^@\^@7\^@77777777777\^@\^@\^@\^@\^@\^@\^@77777777777777777777777777\^@7\^@\^@7\^@77777777777777777777777777\^@\^@\^@\^@\^@", LexEngine.next0x1 "\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^O\^@")
end
in
fun lexMain s = LexEngine.lex {lexMain=lexMain} Tables.lexMain s
end
end
