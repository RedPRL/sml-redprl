structure ExprParser :
sig
  val parseExpr
    : AstSignature.sign
    -> (Sort.t -> Ast.ast CharParser.charParser)
    -> Ast.ast ParserCombinators.fixityitem CharParser.charParser
end =
struct
  open CharParser ParserCombinators RedTokenParser
  open Ast OperatorData NominalLcfOperatorData CttOperatorData AtomsOperatorData SortData RecordOperatorData
  infix $ \ $#

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  val rec inferRefinedSort =
    fn CTT (BASE tau) $ _ => tau
     | _ => EXP

  fun inferRefinedSort' m =
    succeed (inferRefinedSort m)
      handle e => fail (exnMessage e)

  val parseSymbol = identifier
  val parseVariable = identifier

  fun parseExpr sign f =
    let
      val parseHypVar =
        symbol "@" >> parseSymbol
          wth (fn u => LCF (HYP_VAR u) $ [])

      val parseAx =
        symbol "Ax"
          return (CTT AX $ [])

      val parseUniv =
        symbol "Univ"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          && (parens (f LVL))
          wth (fn (tau, i) =>
            CTT (UNIV tau) $ [([],[]) \ i])

      val parseCApprox =
        symbol "<="
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f tau) wth (fn (m1, m2) =>
              CTT (CAPPROX tau) $ [([],[]) \ m1, ([],[]) \ m2]))

      val parseCEquiv =
        symbol "~"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f tau) wth (fn (m1, m2) =>
              CTT (CEQUIV tau) $ [([],[]) \ m1, ([],[]) \ m2]))

      val parseBase =
        symbol "Base"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          wth (fn tau =>
            CTT (BASE tau) $ [])

      val parseDFun =
        symbol "dfun"
          >> parens (f EXP << semi && squares parseVariable << dot && f EXP)
          wth (fn (a, (x, b)) =>
            CTT DFUN $ [([],[]) \ a, ([],[x]) \ b])

      val parseDepIsect =
        symbol "disect"
          >> parens (f EXP << semi && squares parseVariable << dot && f EXP)
          wth (fn (a, (x, b)) =>
            CTT DEP_ISECT$ [([],[]) \ a, ([],[x]) \ b])

      val parseFun =
        symbol "fun"
          >> parens (f EXP << semi && f EXP)
          wth (fn (a, b) =>
            CTT FUN $ [([],[]) \ a, ([],[]) \ b])

      val parseLam =
        symbol "lam"
          >> parens (squares parseVariable << dot && f EXP)
          wth (fn (x, m) =>
            CTT LAM $ [([],[x]) \ m])

      val parseAp =
        symbol "ap"
          >> parens (f EXP << semi && f EXP)
          wth (fn (m, n) =>
            CTT AP $ [([],[]) \ m, ([],[]) \ n])

      val parseAtom =
        symbol "Atom"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          wth (fn tau =>
            ATM (ATOM tau) $ [])

      val parseToken =
        symbol "'"
          >> parseSymbol
          && ((colon >> SortParser.parseSort sign) || succeed EXP)
          wth (fn (u, tau) =>
            ATM (TOKEN (u,tau)) $ [])

      val parseTest =
        symbol "ifeq"
          >> (braces (SortParser.parseSort sign << comma && SortParser.parseSort sign) || succeed (EXP, EXP))
          -- (fn (sigma, tau) =>
            parens (f EXP << semi && f EXP << semi && f tau << semi && f tau)
              wth (fn (t1, (t2, (yes, no))) =>
                ATM (TEST (EXP, EXP)) $ [([],[]) \ t1, ([],[]) \ t2, ([],[]) \ yes, ([],[]) \ no]))

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
              CTT (EQ tau) $ [([],[]) \ m1, ([],[]) \ m2, ([],[]) \ a]))

      val parseMember =
        symbol "member"
          >> (braces (SortParser.parseSort sign) || succeed EXP)
          -- (fn tau =>
            parens (f tau << semi && f EXP) wth (fn (m, a) =>
              CTT (MEMBER tau) $ [([],[]) \ m, ([],[]) \ a]))

      val parseSquash =
        symbol "Squash" >> parens parseRefinement
          wth (fn (a, tau) =>
             CTT (SQUASH tau) $ [([],[]) \ a])

      val parseEnsemble =
        braces @@
          parseVariable << colon
            && parseRefinement << symbol "|"
            && parseRefinement
            wth (fn (x, ((a,tau1), (b,tau2))) =>
              CTT (ENSEMBLE (tau1, tau2)) $ [([],[]) \ a, ([],[x]) \ b])

      val parseRcdCons =
        symbol "cons"
          >> squares parseSymbol
          && parens (f EXP << semi && f EXP)
          wth (fn (lbl, (hd, tl)) =>
            RCD (CONS lbl) $ [([],[]) \ hd, ([],[]) \ tl])

      val parseRcdProj =
        symbol "#"
          >> parseSymbol
          && parens (f EXP)
          wth (fn (lbl, rcd) =>
            RCD (PROJ lbl) $ [([],[]) \ rcd])

      local
        val parseRcdItem =
          parseSymbol
            << symbol "="
            && f EXP

        fun rcons ((lbl, m), tl) =
          RCD (CONS lbl) $ [([],[]) \ m, ([],[]) \ tl]
      in
        val parseRcdLiteral =
          braces (commaSep parseRcdItem)
            wth (List.foldl rcons (CTT AX $ []))
      end

      local
        val parseRecordItem =
          parseSymbol
            << colon
            && f EXP

        fun record ((lbl, m), tl) =
          RCD (RECORD lbl) $ [([], []) \ m, ([], [lbl]) \ tl]

        val makeTop = CTT (TOP EXP) $ []
      in
        val parseRecordTy =
          braces (commaSep parseRecordItem)
            wth (List.foldr record makeTop)
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
            Postfix (12, fn m => RCD (PROJ lbl) $ [([],[]) \ m]))

      val parseFixity =
        parsePostfixProj wth Opr
    in
      parseAtomic || parseFixity
    end
end
