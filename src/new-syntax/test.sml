structure Test =
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

  fun parse text =
    let
      val lexer = RedPrlParser.makeLexer (stringreader text) ""
      val (res,_) = RedPrlParser.parse(1, lexer, error, "")
    in
      res
    end


    (*
  fun test text =
    print ("\n" ^ RedPrlAst.toString (parse text) ^ "\n\n")

    *)

  fun testFile fileName =
    let
      val input = TextIO.inputAll (TextIO.openIn fileName)
    in
      print ("\n" ^ Signature.toString (parse input))
    end

end
