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

  fun parseElt fileName lexer =
    RedPrlParser.parse (0, lexer, error fileName, fileName)

  local
    open Signature
  in
    fun processElt sign (DECL (nm, d, pos)) = Signature.insert sign nm (d, SOME pos)
      | processElt sign (CMD c) = Signature.command sign c
  end

  fun logExn exn =
    RedPrlLog.print RedPrlLog.FAIL (RedPrlError.annotation exn, RedPrlError.format exn)

  local
    val EOF = RedPrlLrVals.Tokens.EOF (Coord.init, Coord.init)
    val DEF = RedPrlLrVals.Tokens.DCL_DEF (Coord.init, Coord.init)
    val THM = RedPrlLrVals.Tokens.DCL_THM (Coord.init, Coord.init)
    val TAC = RedPrlLrVals.Tokens.DCL_TAC (Coord.init, Coord.init)
    val PRINT = RedPrlLrVals.Tokens.CMD_PRINT (Coord.init, Coord.init)

    fun isBeginElt tok =
      RedPrlParser.Token.sameToken (tok, THM) orelse
      RedPrlParser.Token.sameToken (tok, DEF) orelse
      RedPrlParser.Token.sameToken (tok, TAC) orelse
      RedPrlParser.Token.sameToken (tok, PRINT)

    fun isEof tok =
      RedPrlParser.Token.sameToken (tok, EOF)

    fun skipToBeginElt lexer =
      let
        val (next_tok, lexer') = RedPrlParser.Stream.get lexer
      in
        if isEof next_tok orelse isBeginElt next_tok
        then lexer
        else skipToBeginElt lexer'
      end

    fun recover lexer =
      let
        val (_, lexer) = RedPrlParser.Stream.get lexer
      in
        skipToBeginElt lexer
      end

    fun doElt fileName lexer sign =
      let
        val (elt, lexer) = parseElt fileName lexer
      in
        (true, processElt sign elt, lexer)
      end
      handle exn => (logExn exn; (false, sign, recover lexer))
  in
    fun parseSig fileName =
      let
        fun loop acc lexer sign =
          let
            val (next_tok, _) = RedPrlParser.Stream.get lexer
          in
            if RedPrlParser.Token.sameToken (next_tok, EOF)
            then (acc, sign)
            else
              let
                val (err, sign, lexer) = doElt fileName lexer sign
              in
                loop (acc andalso err) lexer sign
              end
          end

        val input = TextIO.inputAll (TextIO.openIn fileName)
        val lexer = RedPrlParser.makeLexer (stringreader input) fileName
      in
        loop true lexer Signature.empty
      end
  end

  fun processFile fileName =
    let
      val (noParseErrors, sign) = parseSig fileName
    in
      Signature.check sign andalso noParseErrors
    end
    handle exn => (logExn exn; false)
end
