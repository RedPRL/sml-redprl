structure Frontend =
struct
  fun stringreader s =
    let
      val pos = ref 0
      val remainder = ref (String.size s)
      fun min(a, b) = if a < b then a else b
    in
      fn n =>
        let
          val m = min(n, !remainder)
          val s = String.substring(s, !pos, m)
          val () = pos := !pos + m
          val () = remainder := !remainder - m
        in
          s
        end
    end

  exception ParseError of Pos.t * string

  fun error fileName (s, pos, pos') : unit =
    raise ParseError (Pos.pos (pos fileName) (pos' fileName), s)

  fun processFile fileName =
    let
      val input = TextIO.inputAll (TextIO.openIn fileName)
      val lexer = RedPrlParser.makeLexer (stringreader input) fileName
      val (sign, _) = RedPrlParser.parse (1, lexer, error fileName, fileName)
    in
      Signature.check sign
    end
    handle ParseError (pos, msg) => (RedPrlLog.print RedPrlLog.FAIL (SOME pos, msg); false)
         | exn => (RedPrlLog.print RedPrlLog.FAIL (SOME (Pos.pos (Coord.init fileName) (Coord.init fileName)), RedPrlError.format exn); false)
end
