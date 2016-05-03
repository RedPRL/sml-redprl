structure TacParser :
sig
  type metavariable_table = string -> Ast.metavariable * Valence.t

  val parseMultitac
    : AstSignature.sign
    -> metavariable_table
    -> (Sort.t -> Ast.ast CharParser.charParser)
    -> Ast.ast ParserCombinators.fixityitem CharParser.charParser

  val parseTac
    : AstSignature.sign
    -> metavariable_table
    -> (Sort.t -> Ast.ast CharParser.charParser)
    -> Ast.ast ParserCombinators.fixityitem CharParser.charParser
end =
struct
  type metavariable_table = string -> Ast.metavariable * Valence.t

  open CharParser ParserCombinators RedTokenParser
  open Ast OperatorData NominalLcfOperatorData CttOperatorData AtomsOperatorData SortData RecordOperatorData
  infix $ \ $#

  infixr 4 << >>
  infixr 3 &&
  infix  2 --
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  val parseSymbol = identifier
  val parseVariable = identifier

  fun parseMultitac sign rho f =
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

      val parseChkInf =
        symbol "chk-inf"
          return (LCF CHKINF $ [])

      val parseExt =
        symbol "ext"
          return (LCF EXT $ [])

      val parseCum =
        symbol "cumulativity"
          return (LCF CUM $ [])

      val parseTrace =
        symbol "trace"
          >> (braces (SortParser.parseSort sign) || succeed SortData.STR)
          -- (fn tau =>
           f tau wth (fn m =>
             LCF (TRACE tau) $ [([],[]) \ m]))

      val parseRewriteGoal =
        symbol "rewrite-goal"
          >> (braces (SortParser.parseSort sign) || succeed SortData.EXP)
          -- (fn tau =>
            f tau wth (fn m =>
              LCF (REWRITE_GOAL tau) $ [([],[]) \ m]))

      val parseTarget =
        opt (symbol "in" >> parseSymbol)

      val parseEvalGoal =
        symbol "eval"
          >> parseTarget
          wth (fn targ =>
            LCF (EVAL_GOAL targ) $ [])

      val parseUnfold =
        symbol "unfold"
          >> parseSymbol
          && parseTarget
          wth (fn (opid, targ) =>
            LCF (UNFOLD (opid, targ)) $ [])

      val parseNormalize =
        symbol "normalize"
          >> parseTarget
          wth (fn targ =>
            LCF (NORMALIZE targ) $ [])

      val parseWitness =
        symbol "witness"
          >> (braces (SortParser.parseSort sign) || succeed SortData.EXP)
          -- (fn tau =>
            squares (f tau) wth (fn m =>
              LCF (WITNESS tau) $ [([],[]) \ m]))

      val parseHyp =
        symbol "hyp"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed EXP))
          wth (fn (u, tau) => LCF (HYP (u, tau)) $ [])

      val parseElim =
        symbol "elim"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed EXP))
          wth (fn (u, tau) => LCF (ELIM (u, tau)) $ [])

      val parseIntro =
        symbol "intro"
          return (LCF (INTRO {rule = NONE}) $ [])

      val parseAuto =
        symbol "auto"
          return (LCF AUTO $ [])

      val parseUnhide =
        symbol "unhide"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed EXP))
          wth (fn (u, tau) => LCF (UNHIDE (u, tau)) $ [])

      val parseRec =
        symbol "rec" >> parseVariable << dot
          && braces (f TAC)
          wth (fn (x, tac) =>
            LCF REC $
              [([], [x]) \ tac])

      val parseOrElse =
        symbol "||"
          return Infix (Right, 7, fn (m, n) =>
            LCF ORELSE $ [([],[]) \ m, ([],[]) \ n])

      val parseProgress =
        symbol "progress" >> parens (f TAC)
          wth (fn t =>
            LCF PROGRESS $ [([],[]) \ t])

      val parseAtomicTac =
        (parseId
          || parseFail
          || parseCStep
          || parseCEval
          || parseCSym
          || parseEq
          || parseChkInf
          || parseExt
          || parseTrace
          || parseCum
          || parseHyp
          || parseElim
          || parseIntro
          || parseUnhide
          || parseAuto
          || parseRec
          || parseRewriteGoal
          || parseEvalGoal
          || parseWitness
          || parseUnfold
          || parseNormalize
          || parseProgress
          || GenericParser.parseGeneric sign rho f TAC) wth Atm

      val parseFixityTac =
        parseOrElse wth Opr

      val parseAll =
        parsefixity (parseFixityTac || parseAtomicTac)
          wth (fn t =>
            LCF ALL $ [([], []) \ t])

      val parseEach =
        f (VEC TAC)
          wth (fn v =>
            LCF EACH $ [([], []) \ v])

      val parseFocus =
        symbol "#"
          >> integer
          && braces (f TAC)
          wth (fn (i, tac) =>
            LCF (FOCUS i) $
              [([],[]) \ tac])
    in
      (parseEach
        || parseFocus
        || parseAll) wth Atm
    end

  fun parseTac sign rho f =
    let
      datatype component = BINDING of (symbol * sort) list * ast

      val parseComponent =
        (commaSep1 (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed EXP)) << symbol "<-" || succeed [])
          && f MTAC
          wth BINDING

      fun makeSeq mt (us : (symbol * sort) list) t =
        let
          val us1 = map #1 us
        in
          LCF (SEQ (map #2 us)) $
            [([],[]) \ mt, (us1, []) \ t]
        end

      val multitacToTac =
        fn (LCF ALL $ [_ \ t]) => t
         | mt => makeSeq mt [] (LCF ID $ [])

      val rec compileScript =
        fn [] => fail "Expected tactic script"
         | [BINDING (_, tac)] => succeed (multitacToTac tac)
         | BINDING (us, tac) :: ts =>
             compileScript ts
               wth makeSeq tac us
    in
      (sepEnd1' parseComponent semi
        -- compileScript) wth Atm
    end

end
