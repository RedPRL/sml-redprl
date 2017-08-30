
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
          val comma : info -> t
          val double_right_arrow : info -> t
          val end_ : info -> t
          val eof : info -> t
          val equals : info -> t
          val error : info -> t
          val exact : info -> t
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
initial state = 45
total states = 57

-----

lexmain state 12 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 40   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 13 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 29   (final:exact)
117-122 => state 25   (final:ident)

-----

lexmain state 14 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 18   (final:ident)
111-122 => state 25   (final:ident)

-----

lexmain state 15 (final:print):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 16 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-113 => state 25   (final:ident)
114 => state 54   (final:ident)
115-122 => state 25   (final:ident)

-----

lexmain state 17 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 22   (final:ident)
111-119 => state 25   (final:ident)
120 => state 34   (final:ident)
121-122 => state 25   (final:ident)

-----

lexmain state 18 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 49   (final:refine)
102-122 => state 25   (final:ident)

-----

lexmain state 19 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-107 => state 25   (final:ident)
108 => state 36   (final:bool)
109-122 => state 25   (final:ident)

-----

lexmain state 20 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 15   (final:print)
117-122 => state 25   (final:ident)

-----

lexmain state 21 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 39   (final:prove)
102-122 => state 25   (final:ident)

-----

lexmain state 22 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-99 => state 25   (final:ident)
100 => state 53   (final:end_)
101-122 => state 25   (final:ident)

-----

lexmain state 23 (final:error):

49 => state 9   (sink:proj1)
50 => state 8   (sink:proj2)

-----

lexmain state 24 (final:let_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

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

lexmain state 26 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-101 => state 25   (final:ident)
102 => state 32   (final:ident)
103-122 => state 25   (final:ident)

-----

lexmain state 27 (final:tt):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 28 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-98 => state 25   (final:ident)
99 => state 13   (final:ident)
100-122 => state 25   (final:ident)

-----

lexmain state 29 (final:exact):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 30 (final:skip):

9-10 => state 30   (final:skip)
13 => state 30   (final:skip)
32 => state 30   (final:skip)

-----

lexmain state 31 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-117 => state 25   (final:ident)
118 => state 21   (final:ident)
119-122 => state 25   (final:ident)

-----

lexmain state 32 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-104 => state 25   (final:ident)
105 => state 14   (final:ident)
106-122 => state 25   (final:ident)

-----

lexmain state 33 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 19   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 34 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97 => state 28   (final:ident)
98-122 => state 25   (final:ident)

-----

lexmain state 35 (final:in_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 36 (final:bool):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 37 (final:ident):

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

lexmain state 38 (final:fn_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 39 (final:prove):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 40 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97 => state 46   (final:ident)
98-122 => state 25   (final:ident)

-----

lexmain state 41 (final:equals):

62 => state 6   (sink:double_right_arrow)

-----

lexmain state 42 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 27   (final:tt)
117-122 => state 25   (final:ident)

-----

lexmain state 43 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 44 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 26   (final:ident)
102-122 => state 25   (final:ident)

-----

lexmain state 45 (initial, final:error):

0-8 => state 2   (sink:error)
9-10 => state 47   (final:skip)
11-12 => state 2   (sink:error)
13 => state 47   (final:skip)
14-31 => state 2   (sink:error)
32 => state 47   (final:skip)
33-34 => state 2   (sink:error)
35 => state 23   (final:error)
36-39 => state 2   (sink:error)
40 => state 1   (sink:lparen)
41 => state 10   (sink:rparen)
42-43 => state 2   (sink:error)
44 => state 7   (sink:comma)
45 => state 43   (final:ident)
46 => state 2   (sink:error)
47 => state 43   (final:ident)
48-60 => state 2   (sink:error)
61 => state 41   (final:equals)
62-64 => state 2   (sink:error)
65-90 => state 43   (final:ident)
91 => state 3   (sink:lsquare)
92 => state 43   (final:ident)
93 => state 4   (sink:rsquare)
94-95 => state 2   (sink:error)
96 => state 5   (sink:backtick)
97 => state 43   (final:ident)
98 => state 55   (final:ident)
99-100 => state 43   (final:ident)
101 => state 17   (final:ident)
102 => state 50   (final:ident)
103 => state 12   (final:ident)
104 => state 43   (final:ident)
105 => state 51   (final:ident)
106-107 => state 43   (final:ident)
108 => state 52   (final:ident)
109-111 => state 43   (final:ident)
112 => state 16   (final:ident)
113 => state 43   (final:ident)
114 => state 44   (final:ident)
115 => state 43   (final:ident)
116 => state 42   (final:ident)
117-122 => state 43   (final:ident)
123-127 => state 2   (sink:error)
EOS => state 11   (sink:eof)

-----

lexmain state 46 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-107 => state 25   (final:ident)
108 => state 48   (final:goal)
109-122 => state 25   (final:ident)

-----

lexmain state 47 (final:skip):

9-10 => state 30   (final:skip)
13 => state 30   (final:skip)
32 => state 30   (final:skip)

-----

lexmain state 48 (final:goal):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 49 (final:refine):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 50 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 38   (final:fn_)
111-122 => state 25   (final:ident)

-----

lexmain state 51 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-109 => state 25   (final:ident)
110 => state 35   (final:in_)
111-122 => state 25   (final:ident)

-----

lexmain state 52 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-100 => state 25   (final:ident)
101 => state 56   (final:ident)
102-122 => state 25   (final:ident)

-----

lexmain state 53 (final:end_):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-122 => state 25   (final:ident)

-----

lexmain state 54 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-104 => state 25   (final:ident)
105 => state 37   (final:ident)
106-110 => state 25   (final:ident)
111 => state 31   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 55 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-110 => state 25   (final:ident)
111 => state 33   (final:ident)
112-122 => state 25   (final:ident)

-----

lexmain state 56 (final:ident):

39 => state 25   (final:ident)
45 => state 25   (final:ident)
47-57 => state 25   (final:ident)
65-90 => state 25   (final:ident)
92 => state 25   (final:ident)
95 => state 25   (final:ident)
97-115 => state 25   (final:ident)
116 => state 24   (final:let_)
117-122 => state 25   (final:ident)

*)

struct
local
structure LexEngine = LexEngineFun (structure Streamable = Streamable
type symbol = Arg.symbol
val ord = Arg.ord)
structure Tables = struct
fun epsilon _ = raise (Fail "Illegal lexeme")
val lexmain = (45, 11, 56, Vector.fromList [Arg.lparen,Arg.error,Arg.lsquare,Arg.rsquare,Arg.backtick,Arg.double_right_arrow,Arg.comma,Arg.proj2,Arg.proj1,Arg.rparen,Arg.eof,Arg.ident,Arg.ident,Arg.ident,Arg.print,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.error,Arg.let_,Arg.ident,Arg.ident,Arg.tt,Arg.ident,Arg.exact,Arg.skip,Arg.ident,Arg.ident,Arg.ident,Arg.ident,Arg.in_,Arg.bool,Arg.ident,Arg.fn_,Arg.prove,Arg.ident,Arg.equals,Arg.ident,Arg.ident,Arg.ident,Arg.error,Arg.ident,Arg.skip,Arg.goal,Arg.refine,Arg.ident,Arg.ident,Arg.ident,Arg.end_,Arg.ident,Arg.ident,Arg.ident], LexEngine.next7x1 128 "\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y(\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^]\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^R\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y6\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^V\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\"\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y1\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y$\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^O\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y'\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y5\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\t\b\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y \^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\r\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^^\^^\^@\^@\^^\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^^\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^U\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^N\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^S\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^\\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^T\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@.\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^F\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^[\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Z\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^B\^B\^B\^B\^B\^B\^B\^B\^B//\^B\^B/\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B/\^B\^B\^W\^B\^B\^B\^B\^A\n\^B\^B\a+\^B+\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B\^B)\^B\^B\^B++++++++++++++++++++++++++\^C+\^D\^B\^B\^E+7++\^Q2\f+3++4+++\^P+,+*++++++\^B\^B\^B\^B\^B\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y0\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^^\^^\^@\^@\^^\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^^\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y&\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y#\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y8\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y%\^Y\^Y\^Y\^Y\^Y\^_\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y!\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^Y\^@\^@\^@\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@\^@\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^@\^Y\^@\^@\^Y\^@\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^Y\^X\^Y\^Y\^Y\^Y\^Y\^Y\^@\^@\^@\^@\^@", LexEngine.next0x1 "\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\v\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@\^@")
end
in
fun lexmain s = LexEngine.lex {lexmain=lexmain} Tables.lexmain s
end
end
