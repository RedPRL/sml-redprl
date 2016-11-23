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

  local
    structure E = RedPrlError
  in
    fun error fileName (s, pos, pos') : unit =
      raise E.annotate (SOME (Pos.pos (pos fileName) (pos' fileName)))
            (RedPrlError.error [E.% s])
  end

  fun parseSig fileName =
    let
      val input = TextIO.inputAll (TextIO.openIn fileName)
      val lexer = RedPrlParser.makeLexer (stringreader input) fileName
      val (sign, _) = RedPrlParser.parse (1, lexer, error fileName, fileName)
    in
      sign
    end

  fun processFile fileName =
    Signature.check (parseSig fileName)
    handle exn => (RedPrlLog.print RedPrlLog.FAIL (RedPrlError.annotation exn, RedPrlError.format exn); false)

end
