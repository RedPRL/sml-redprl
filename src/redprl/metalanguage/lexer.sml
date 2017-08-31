structure MetalanguageLexAction = 
struct
  structure T = MetalanguageParseAction

  type coord = Coord.t
  type pos = Pos.t
  type token = T.terminal

  type symbol = coord * char
  val ord = fn (_, c) => Int.min (128, Char.ord c)
  type t = (token * pos) Stream.front

  type self = {lexmain: symbol StreamStreamable.t -> t}
  type info =
    {match: symbol list,
     len: int,
     start: symbol StreamStreamable.t,
     follow: symbol StreamStreamable.t,
     self: self}

  fun @@ (f, x) = f x
  infixr @@

  exception hole
  fun ?e = raise e
  fun ?! _ = ?hole

  (* Some of this code is cribbed from Chris Martens' implementation of Ceptre. *)

  fun posRange (toks: symbol list) = 
    Pos.pos (#1 (List.hd toks)) (#1 (List.last toks))

  fun stringRange (toks: symbol list) = 
    String.implode (List.map #2 toks)

  fun eof _ =
    Stream.Nil

  fun error ({match, ...} : info) = 
    case match of
       [] => RedPrlError.raiseError @@ RedPrlError.GENERIC [Fpp.text "Encountered unexpected error with lexing"]
     | _ => RedPrlError.raiseAnnotatedError (posRange match, RedPrlError.GENERIC [Fpp.text @@ "Encountered error lexing \"" ^ stringRange match ^"\""])

  fun skip ({self, follow, ...} : info) =
    #lexmain self follow

  fun ident ({self, match, follow, ...} : info) =
    let
      val pos = posRange match
    in
      Stream.Cons
        ((T.IDENT (pos, stringRange match), pos),
         Stream.lazy (fn () => #lexmain self follow))
    end

  fun simple token ({self, match, follow, ...}: info) =
    let
      val pos = posRange match
    in
      Stream.Cons
        ((token pos, pos), 
         Stream.lazy (fn () => #lexmain self follow))
    end

  val lparen = simple T.LPAREN
  val rparen = simple T.RPAREN
  val lsquare = simple T.LSQUARE
  val rsquare = simple T.RSQUARE
  val let_ = simple T.LET
  val fn_ = simple T.FN
  val val_ = simple T.VAL
  val proj1 = simple T.PROJ1
  val proj2 = simple T.PROJ2
  val in_ = simple T.IN
  val by = simple T.BY
  val end_ = simple T.END
  val comma = simple T.COMMA
  val semi = simple T.SEMI
  val double_right_arrow = simple T.DOUBLE_RIGHT_ARROW
  val equals = simple T.EQUALS
  val print = simple T.PRINT
  val goal = simple T.GOAL
  val prove = simple T.PROVE
  val backtick = simple T.BACKTICK
  val bool = simple T.BOOL
  val tt = simple T.TT
  val ff = simple T.FF
  val exact = simple T.EXACT
  val refine = simple T.REFINE
  val wbool = simple T.WBOOL
end

structure MetalanguageLex = MetalanguageLexFn (structure Streamable = StreamStreamable and Arg = MetalanguageLexAction)