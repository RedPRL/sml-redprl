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
    fun error fileName (s, pos, pos') =
      raise E.annotate (SOME (Pos.pos (pos fileName) (pos' fileName)))
            (RedPrlError.error [Fpp.text s])
  end

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
    val DOT = RedPrlLrVals.Tokens.DOT (Coord.init, Coord.init)

    fun isBeginElt tok =
      RedPrlParser.Token.sameToken (tok, THM) orelse
      RedPrlParser.Token.sameToken (tok, DEF) orelse
      RedPrlParser.Token.sameToken (tok, TAC) orelse
      RedPrlParser.Token.sameToken (tok, PRINT)

    fun isEof tok =
      RedPrlParser.Token.sameToken (tok, EOF)

    fun isDot tok =
      RedPrlParser.Token.sameToken (tok, DOT)

    fun getPos (RedPrlParser.Token.TOKEN (_, (_, c_start, c_end))) =
      (c_start, c_end)

    fun skipDot fileName lexer =
      let
        val (next_tok, lexer') = RedPrlParser.Stream.get lexer
      in
        if isDot next_tok
        then lexer'
        else
          let
            val (c1, c2) = getPos next_tok
          in
            error fileName ("Expected '.' after element.", c1, c2)
          end
      end

    fun parseElt fileName lexer =
      let
        val (elt, lexer) = RedPrlParser.parse (0, lexer, error fileName, fileName)
        val lexer = skipDot fileName lexer
      in
        (elt, lexer)
      end

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
    fun parseSig fileName buf =
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

        val lexer = RedPrlParser.makeLexer (stringreader buf) fileName
      in
        loop true lexer Signature.empty
      end
  end

  fun processBuffer fileName buf =
    let
      val (noParseErrors, sign) = parseSig fileName buf
    in
      Signature.check sign andalso noParseErrors
    end
    handle exn => (logExn exn; false)

  fun processStream fileName stream =
    let
      val input = TextIO.inputAll stream
    in
      processBuffer fileName input
    end

  fun processFile fileName =
    processStream fileName (TextIO.openIn fileName)
end
