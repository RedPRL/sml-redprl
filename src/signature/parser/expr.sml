structure ExprParser :
sig
  val parseExpr
    : AstSignature.sign
    -> (AstSignature.sort -> AstSignature.term CharParser.charParser)
    -> AstSignature.term ParserCombinators.fixityitem CharParser.charParser
end =
struct
  open CharParser ParserCombinators RedTokenParser SortData
  structure Syn = RedPrlAstSyntax

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  fun inferRefinedSort tm =
    case Syn.out tm of
       Syn.BASE tau => tau
     | _ => SortData.EXP

  fun inferRefinedSort' m =
    succeed (inferRefinedSort m)
      handle e => fail (exnMessage e)

  val parseSymbol = identifier
  val parseVariable = identifier

  fun parseExpr sign f =
    let
      val parseHypVar =
        symbol "@" >> parseSymbol
          wth (Syn.into o Syn.HYP_REF)

      val parseAx =
        symbol "Ax"
          return (Syn.into Syn.AX)

      val parseUniv =
        symbol "Univ"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          && (parens (f LVL))
          wth (Syn.into o Syn.UNIV)

      val parseCApprox =
        symbol "<="
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f tau) wth (fn (m1, m2) =>
              Syn.into (Syn.CAPPROX (tau, m1, m2))))

      val parseCEquiv =
        symbol "~"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f tau) wth (fn (m1, m2) =>
              Syn.into (Syn.CEQUIV (tau, m1, m2))))

      val parseBase =
        symbol "Base"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          wth (Syn.into o Syn.BASE)

      val parseDFun =
        symbol "dfun"
          >> parens (f EXP << semi && squares parseVariable << dot && f EXP)
          wth (fn (a, (x, b)) =>
            Syn.into (Syn.DFUN (a, x, b)))

      val parseDepIsect =
        symbol "disect"
          >> parens (f EXP << semi && squares parseVariable << dot && f EXP)
          wth (fn (a, (x, b)) =>
            Syn.into (Syn.DEP_ISECT (a, x, b)))

      val parseFun =
        symbol "fun"
          >> parens (f EXP << semi && f EXP)
          wth (Syn.into o Syn.FUN)

      val parseLam =
        symbol "lam"
          >> parens (squares parseVariable << dot && f EXP)
          wth (Syn.into o Syn.LAM)

      val parseAp =
        symbol "ap"
          >> parens (f EXP << semi && f EXP)
          wth (Syn.into o Syn.AP)

      val parseAtom =
        symbol "Atom"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          wth (Syn.into o Syn.ATOM)

      val parseToken =
        symbol "'"
          >> parseSymbol
          && ((colon >> SortParser.parseSort sign) || succeed EXP)
          wth (Syn.into o Syn.TOKEN)

      val parseTest =
        symbol "ifeq"
          >> (braces (SortParser.parseSort sign << comma && SortParser.parseSort sign) || succeed (EXP, EXP))
          -- (fn (sigma, tau) =>
            parens (f EXP << semi && f EXP << semi && f tau << semi && f tau)
              wth (fn (t1, (t2, (yes, no))) =>
                Syn.into (Syn.IF_EQ (EXP, EXP, t1, t2, yes, no))))

      fun @@ (f,x) = f x
      infix @@

      val parseRefinement =
        f EXP -- (fn a =>
          ((symbol "<:" >> SortParser.parseSort sign) || inferRefinedSort' a)
            wth (fn tau =>
              (a,tau)))

      val parseEq =
        symbol "="
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f tau << semi && f EXP) wth (fn (m1, (m2, a)) =>
              Syn.into (Syn.EQ (tau, m1, m2, a))))

      val parseMember =
        symbol "member"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f EXP) wth (fn (m, a) =>
              Syn.into (Syn.MEMBER (tau, m, a))))

      val parseSquash =
        symbol "Squash" >> parens parseRefinement
          wth (fn (a, tau) =>
             Syn.into (Syn.SQUASH (tau, a)))

      val parseEnsemble =
        braces @@
          parseVariable << colon
            && parseRefinement << symbol "|"
            && parseRefinement
            wth (fn (x, ((a,tau1), (b,tau2))) =>
              Syn.into (Syn.ENSEMBLE (tau1, tau2, a, x, b)))

      val parseRcdCons =
        symbol "cons"
          >> squares parseSymbol
          && parens (f EXP << semi && f EXP)
          wth (fn (lbl, (hd, tl)) =>
            Syn.into (Syn.RCD_CONS (lbl, hd, tl)))

      val parseRcdProj =
        symbol "#"
          >> parseSymbol
          && parens (f EXP)
          wth (Syn.into o Syn.RCD_PROJ)

      local
        val parseRcdItem =
          parseSymbol
            << symbol "="
            && f EXP

        fun rcons ((lbl, m), tl) =
          Syn.into (Syn.RCD_CONS (lbl, m, tl))
      in
        val parseRcdLiteral =
          braces (commaSep parseRcdItem)
            wth (List.foldl rcons (Syn.into Syn.AX))
      end

      local
        val parseRecordItem =
          parseSymbol
            << colon
            && f EXP

        fun record ((lbl, m), tl) =
          Syn.into (Syn.RECORD_TY (lbl, m, lbl, tl))
      in
        val parseRecordTy =
          braces (commaSep parseRecordItem)
            wth (List.foldr record (Syn.into (Syn.TOP EXP)))
      end

      val parseAtomic =
       (parseCApprox
         || parseCEquiv
         || parseAx
         || parseUniv
         || parseEq
         || parseMember
         || parseBase
         || parseDFun
         || parseDepIsect
         || parseFun
         || parseLam
         || parseAp
         || parseAtom
         || parseToken
         || parseTest
         || parseSquash
         || parseEnsemble
         || parseRecordTy
         || parseRcdCons
         || parseRcdLiteral
         || parseRcdProj
         || parseHypVar) wth Atm

      val parsePostfixProj =
        symbol "."
          >> parseSymbol
          wth (fn lbl =>
            Postfix (12, fn m => Syn.into (Syn.RCD_PROJ (lbl, m))))

      val parseFixity =
        parsePostfixProj wth Opr
    in
      parseAtomic || parseFixity
    end
end
