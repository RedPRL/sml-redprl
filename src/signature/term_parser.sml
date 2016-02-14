structure TermParser : TERM_PARSER =
struct
  type metavariable_table = string -> Ast.metavariable * Valence.t

  open ParserCombinators CharParser
  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure LangDef :> LANGUAGE_DEF =
  struct
    type scanner = char charParser
    val commentStart = SOME "(*"
    val commentEnd = SOME "*)"
    val commentLine = SOME "//"
    val nestedComments = true
    val identLetter = letter || digit
    val identStart = identLetter
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = ["Def", "Thm", "Tac", "by"]
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TokenParser = TokenParser (LangDef)
  open TokenParser

  local
    open SortData
  in
    fun parseSort _ =
      ParserCombinators.fix (fn p =>
        symbol "exp" return EXP
        || symbol "lvl" return LVL
        || symbol "tac" return TAC
        || symbol "mtac" return MTAC
        || symbol "vec" >> braces p wth VEC
        || symbol "str" return STR)
  end

  val force =
    ParserCombinators.$

  type 'a parser_family = Sort.t -> 'a charParser
  type 'a endo = 'a -> 'a

  (* to fix a recursive family of parsers *)
  fun fix' (f : 'a parser_family endo) : 'a parser_family =
    fn tau =>
      force (fn () => f (fix' f) tau)

  fun tabulateSeparateN n p q =
    let
      fun go _ 0 = succeed []
        | go 0 n = p 0 && go 1 (n - 1) wth op::
        | go i n = q >> p i && go (i + 1) (n - 1) wth op::
    in
      go 0 n
    end

  fun separateN n p =
    tabulateSeparateN n (fn _ => p)


  datatype hole = !
  fun hole ! = raise Match

  local
    open AstSignature AstSignatureDecl Ast OperatorData NominalLcfOperatorData CttOperatorData LevelOperatorData SortData
    infix $ \ $#
  in
    val rec inferRefinedSort =
      fn CTT (BASE tau) $ _ => tau
       | CTT (UNIV _) $ _ => EXP
       | CTT (CEQUIV _) $ _ => EXP
       | CTT (CAPPROX _) $ _ => EXP
       | CTT (EQ _) $ _ => EXP
       | _ => raise Fail "Could not infer refined sort"

    fun inferRefinedSort' m =
      succeed (inferRefinedSort m)
        handle e => fail (exnMessage e)


    val parseSymbol = identifier
    val parseVariable = identifier

    (* TODO *)
    fun parseTerm' sign rho f =
      fn LVL =>
         let
           val parseBase =
             symbol "lbase"
               wth (fn u =>
                 LVL_OP LBASE $ [])
           val parseSucc =
             symbol "lsuc" >> parens (f LVL)
               wth (fn l =>
                 LVL_OP LSUCC $ [([],[]) \ l])
         in
           try parseSucc
             || parseBase
         end
       | EXP =>
         let
           val parseAx =
             symbol "Ax"
               return (CTT AX $ [])

           val parseUniv =
             symbol "Univ"
               >> (braces (parseSort sign) || succeed EXP)
               && (parens (f LVL))
               wth (fn (tau, i) =>
                 CTT (UNIV tau) $ [([],[]) \ i])

           val parseCApprox =
             symbol "<="
               >> (braces (parseSort sign) || succeed EXP)
               -- (fn tau =>
                 parens (f tau << semi && f tau) wth (fn (m1, m2) =>
                   CTT (CAPPROX tau) $ [([],[]) \ m1, ([],[]) \ m2]))

           val parseCEquiv =
             symbol "~"
               >> (braces (parseSort sign) || succeed EXP)
               -- (fn tau =>
                 parens (f tau << semi && f tau) wth (fn (m1, m2) =>
                   CTT (CEQUIV tau) $ [([],[]) \ m1, ([],[]) \ m2]))

           val parseBase =
             symbol "Base"
               >> (braces (parseSort sign) || succeed EXP)
               wth (fn tau =>
                 CTT (BASE tau) $ [])

           fun @@ (f,x) = f x
           infix @@

           val parseRefinement =
             f EXP -- (fn a =>
               ((symbol "<:" >> parseSort sign) || inferRefinedSort' a)
                 wth (fn tau =>
                   (a,tau)))

           val parseEq =
             symbol "="
               >> (braces (parseSort sign) || succeed EXP)
               -- (fn tau =>
                 parens (f tau << semi && f tau << semi && f EXP) wth (fn (m1, (m2, a)) =>
                   CTT (EQ tau) $ [([],[]) \ m1, ([],[]) \ m2, ([],[]) \ a]))

           val parseMember =
             symbol "member"
               >> (braces (parseSort sign) || succeed EXP)
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
         in
           parseCApprox
             || parseCEquiv
             || parseAx
             || parseUniv
             || parseEq
             || parseMember
             || parseBase
             || parseSquash
             || parseEnsemble
         end
       | VEC tau =>
         squares (commaSep (f tau))
           wth (fn xs =>
             VEC_LIT (tau, length xs) $
               map (fn x => ([], []) \ x) xs)
       | STR =>
         stringLiteral
           wth (fn str =>
             STR_LIT str $ [])
       | TAC =>
         let
           val parseId =
             symbol "id"
               return (LCF ID $ [])

           val parseFail =
             symbol "fail"
               return (LCF FAIL $ [])

           val parseCStep =
             symbol "cstep" >> (braces integer || succeed 1)
               wth (fn i => LCF (CSTEP i) $ [])

           val parseCSym =
             symbol "csym"
               return (LCF CSYM $ [])

           val parseCEval =
             symbol "ceval"
               return (LCF CEVAL $ [])

           val parseEq =
             symbol "eq" >> (opt (braces integer))
               wth (fn rule =>
                 LCF (NominalLcfOperatorData.EQ {rule = rule}) $ [])

           val parseTrace =
             symbol "trace"
               >> (braces (parseSort sign) || succeed SortData.STR)
               -- (fn tau =>
                f tau wth (fn m =>
                  LCF (TRACE tau) $ [([],[]) \ m]))

           val parseRewriteGoal =
             symbol "rewrite-goal"
               >> (braces (parseSort sign) || succeed SortData.EXP)
               -- (fn tau =>
                 f tau wth (fn m =>
                   LCF (REWRITE_GOAL tau) $ [([],[]) \ m]))

           val parseEvalGoal =
             symbol "eval-goal"
               return (LCF EVAL_GOAL $ [])

           val parseWitness =
             symbol "witness"
               >> (braces (parseSort sign) || succeed SortData.EXP)
               -- (fn tau =>
                 f tau wth (fn m =>
                   LCF (WITNESS tau) $ [([],[]) \ m]))

           val parseHyp =
             symbol "hyp"
               >> squares (parseSymbol && ((colon >> parseSort sign) || succeed EXP))
               wth (fn (u, tau) => LCF (HYP (u, tau)) $ [])

           val parseElim =
             symbol "elim"
               >> squares (parseSymbol && ((colon >> parseSort sign) || succeed EXP))
               wth (fn (u, tau) => LCF (ELIM (u, tau)) $ [])

           val parseIntro =
             symbol "intro"
               return (LCF (INTRO {rule = NONE}) $ [])

           val parseAuto =
             symbol "auto"
               return (LCF AUTO $ [])

           val parseUnhide =
             symbol "unhide"
               >> squares (parseSymbol && ((colon >> parseSort sign) || succeed EXP))
               wth (fn (u, tau) => LCF (UNHIDE (u, tau)) $ [])

           fun parseVec tau =
             commaSep (f tau)
               wth (fn xs =>
                 VEC_LIT (tau, length xs) $
                   map (fn x => ([],[]) \ x) xs)

           val parseEach =
             squares (parseVec TAC)
               wth (fn v =>
                 LCF EACH $ [([], []) \ v])

           val parseFocus =
             symbol "#"
               >> integer
               && braces (f TAC)
               wth (fn (i, tac) =>
                 LCF (FOCUS i) $
                   [([],[]) \ tac])

           val parseRec =
             symbol "rec" >> parseVariable << dot
               && braces (f TAC)
               wth (fn (x, tac) =>
                 LCF REC $
                   [([], [x]) \ tac])

           val parseOrElse =
             braces (f TAC) << symbol "||" && braces (f TAC)
               wth (fn (t1, t2) =>
                 LCF ORELSE $ [([],[]) \ t1, ([],[]) \ t2])

           val parseTac =
             parens (f TAC)
               || parseId
               || parseFail
               || parseCStep
               || parseCEval
               || parseCSym
               || parseEq
               || parseTrace
               || parseHyp
               || parseElim
               || parseIntro
               || parseUnhide
               || parseAuto
               || parseRec
               || parseRewriteGoal
               || parseEvalGoal
               || parseWitness
               || parseOrElse
               || try (parseAny sign rho f TAC)

           val parseAll =
             parseTac
               wth (fn t =>
                 LCF ALL $ [([], []) \ t])

           val parseMultitac =
             parens (f MTAC)
               || parseEach
               || parseFocus
               || parseAll
               || try (parseAny sign rho f MTAC)

           datatype component = BINDING of (symbol * sort) list * ast

           val parseComponent =
             (commaSep1 (parseSymbol << colon && parseSort sign) << symbol "<-" || succeed [])
               && parseMultitac
               wth BINDING

           fun makeSeq t (us : (symbol * sort) list) mt =
             LCF (SEQ (map #2 us)) $
               [([],[]) \ t, (map #1 us, []) \ mt]

           val multitacToTac =
             fn (LCF ALL $ [_ \ t]) => t
              | t => makeSeq t [] (LCF ID $ [])

           val rec compileScript =
             fn [] => fail "Expected tactic script"
              | [BINDING (_, tac)] => succeed (multitacToTac tac)
              | BINDING (us, tac) :: ts =>
                  compileScript ts
                    wth makeSeq tac us
         in
           sepEnd1' parseComponent semi
             -- compileScript
         end
       | _ =>
         fail "to be implemented"

    and parseAny sign rho f tau =
      let
        fun parseParameters n =
          squares (separateN n parseSymbol comma)
            || (if n = 0 then succeed [] else fail "")

        val parseCustomOperator =
          identifier -- (fn opid =>
            case Telescope.find sign opid of
                 NONE => fail "opid not in signature"
               | SOME (DEF {parameters, arguments, sort, definiens}) =>
                   parseParameters (length parameters) wth (fn us =>
                     let
                       val params = ListPair.mapEq (fn (u, (_, tau)) => (u, tau)) (us, parameters)
                       val valences = List.map (fn (_, vl) => vl) arguments
                       val arity = (valences, sort)
                     in
                       CUST (opid, params, arity)
                     end))

        val parseExtract =
          symbol "extract"
            >> (braces (parseSort sign) || succeed EXP)
            -- (fn tau =>
              parens (f (THM tau))
                wth (fn m =>
                  EXTRACT tau $ [([],[]) \ m]))

        fun parseSymbols n =
          braces (separateN n parseSymbol comma)
            || (if n = 0 then succeed [] else fail "")

        fun parseVariables n =
          squares (separateN n parseVariable comma)
            || (if n = 0 then succeed [] else fail "")

        val parseMetavariable =
          identifier -- (fn m =>
            succeed (rho m)
              handle _ => fail "")

        fun parseAbs ((sigmas, taus), tau) =
          let
            val m = length sigmas
            val n = length taus
            val parseDot =
              dot return ()
                || (if n + m = 0 then succeed () else fail "")
          in
            parseSymbols m
              && parseVariables n
              << parseDot && f tau
              wth (fn (us, (vs, t)) => (us, vs) \ t)
          end

        fun parseArguments valences =
          parens
            (tabulateSeparateN
              (length valences)
              (fn i => parseAbs (List.nth (valences, i)))
              semi)
            || (if length valences = 0 then succeed [] else fail "")

        val parseCustomApp =
          try parseCustomOperator -- (fn theta =>
            let
              val (valences, tau') = Operator.arity theta
            in
              if tau' = tau then
                parseArguments valences
                  wth (fn args =>
                    theta $ args)
              else
                fail "mismatched sort"
            end)

        fun parseMetaArguments sorts =
          squares
            (tabulateSeparateN
              (length sorts)
              (fn i => f (List.nth (sorts, i)))
              semi)
            || (if length sorts = 0 then succeed [] else fail "")

        val parseMetaApp =
          try parseMetavariable -- (fn (m, ((sigmas, taus), tau')) =>
            if tau = tau' then
              parseSymbols (length sigmas)
                && parseMetaArguments taus
                wth (fn (us, ts) => m $# (us, ts))
            else
              fail "mismatched sort")
      in
        parseCustomApp
          || parseExtract
          || parseMetaApp
          || parseVariable wth `
      end

    fun parseTerm sign rho =
      fix' (fn f => fn tau =>
        parseTerm' sign rho f tau
          || parseAny sign rho f tau)
  end
end

