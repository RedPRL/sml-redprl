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

  fun error (s, pos, pos') = raise Fail (Pos.toString (Pos.pos pos pos') ^ ": " ^ s)

  fun processFile fileName =
    let
      val input = TextIO.inputAll (TextIO.openIn fileName)
      val lexer = RedPrlParser.makeLexer (stringreader input) fileName
      val (sign,_) = RedPrlParser.parse(1, lexer, error, fileName)
    in
      Signature.check sign
    end
end
