structure TacParser :
sig
  type metavariable_table = string -> AstSignature.metavariable * RedPrlAtomicValence.t

  val parseMultitac
    : AstSignature.sign
    -> metavariable_table
    -> (AstSignature.sort -> AstSignature.term CharParser.charParser)
    -> AstSignature.term ParserCombinators.fixityitem CharParser.charParser

  val parseTac
    : AstSignature.sign
    -> metavariable_table
    -> (AstSignature.sort -> AstSignature.term CharParser.charParser)
    -> AstSignature.term ParserCombinators.fixityitem CharParser.charParser
end =
struct
  structure Ast = RedPrlAst
  structure Syn = RedPrlAstSyntax
  type metavariable_table = string -> Ast.metavariable * AstSignature.valence

  open CharParser ParserCombinators RedTokenParser
  (*infix $ \ $#*)

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
          return (Syn.into Syn.TAC_ID)

      val parseFail =
        symbol "fail"
          return (Syn.into Syn.TAC_FAIL)

      val parseCStep =
        symbol "cstep" >> (braces integer || succeed 1)
          wth (Syn.into o Syn.TAC_CSTEP)

      val parseCSym =
        symbol "csym"
          return (Syn.into Syn.TAC_CSYM)

      val parseCEval =
        symbol "ceval"
          return (Syn.into Syn.TAC_CEVAL)

      val parseEq =
        symbol "eq" >> (opt (braces integer))
          wth (Syn.into o Syn.TAC_EQ)

      val parseChkInf =
        symbol "chk-inf"
          return (Syn.into Syn.TAC_CHKINF)

      val parseExt =
        symbol "ext"
          return (Syn.into Syn.TAC_EXT)

      val parseCum =
        symbol "cumulativity"
          return (Syn.into Syn.TAC_CUM)

      val parseTrace =
        symbol "trace"
          >> (braces (SortParser.parseSort sign) || succeed SortData.STR)
          -- (fn tau =>
           f tau wth (fn m =>
             Syn.into (Syn.TAC_TRACE (tau, m))))

      val parseRewriteGoal =
        symbol "rewrite-goal"
          >> (braces (SortParser.parseSort sign) || succeed SortData.EXP)
          -- (fn tau =>
            f tau wth (fn m =>
              Syn.into (Syn.TAC_REWRITE_GOAL (tau, m))))

      val parseTarget =
        opt (symbol "in" >> parseSymbol)

      val parseEvalGoal =
        symbol "eval"
          >> parseTarget
          wth (fn targ =>
            Syn.into (Syn.TAC_EVAL_GOAL targ))

      val parseUnfold =
        symbol "unfold"
          >> parseSymbol
          && parseTarget
          wth (fn (opid, targ) =>
            Syn.into (Syn.TAC_UNFOLD (opid, targ)))

      val parseNormalize =
        symbol "normalize"
          >> parseTarget
          wth (fn targ =>
            Syn.into (Syn.TAC_NORMALIZE targ))

      val parseWitness =
        symbol "witness"
          >> (braces (SortParser.parseSort sign) || succeed SortData.EXP)
          -- (fn tau =>
            squares (f tau) wth (fn m =>
              Syn.into (Syn.TAC_WITNESS (tau, m))))

      val parseHyp =
        symbol "hyp"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed SortData.EXP))
          wth (Syn.into o Syn.TAC_HYP)

      val parseElim =
        symbol "elim"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed SortData.EXP))
          wth (Syn.into o Syn.TAC_ELIM)

      val parseEta =
        symbol "eta"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed SortData.EXP))
          wth (Syn.into o Syn.TAC_ETA)

      val parseIntro =
        symbol "intro"
          return (Syn.into (Syn.TAC_INTRO NONE))

      val parseAuto =
        symbol "auto"
          return (Syn.into Syn.TAC_AUTO)

      val parseUnhide =
        symbol "unhide"
          >> squares (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed SortData.EXP))
          wth (Syn.into o Syn.TAC_UNHIDE)

      val parseRec =
        symbol "rec" >> parseVariable << dot
          && braces (f SortData.TAC)
          wth (Syn.into o Syn.TAC_REC)

      val parseOrElse =
        symbol "||"
          return Infix (Right, 7, Syn.into o Syn.TAC_ORELSE)

      val parseProgress =
        symbol "progress" >> parens (f SortData.TAC)
          wth (Syn.into o Syn.TAC_PROGRESS)

      val parseAtomicTac =
        !! (parseId
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
            || parseEta
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
            || GenericParser.parseGeneric sign rho f SortData.TAC) wth (fn (t, pos) => Atm (Ast.annotate pos t))

      val parseFixityTac =
        parseOrElse wth Opr

      val parseAll =
        !! (parsefixity (parseFixityTac || parseAtomicTac))
          wth (fn (t, pos) => Ast.annotate pos (Syn.into (Syn.MTAC_ALL t)))

      val parseEach =
        f (SortData.VEC SortData.TAC)
          wth (fn v =>
            case Syn.out v of
               Syn.VEC_LITERAL (_, xs) => Syn.into (Syn.MTAC_EACH xs)
             | _ => raise Match)

      val parseFocus =
        symbol "#"
          >> integer
          && braces (f SortData.TAC)
          wth (Syn.into o Syn.MTAC_FOCUS)
    in
      !! (parseEach
        || parseFocus
        || parseAll) wth (fn (t, pos) => Atm (Ast.annotate pos t))
    end

  fun parseTac sign rho f =
    let
      open RedPrlAst SortData
      datatype component = BINDING of (symbol * sort) list * ast

      val parseComponent =
        (commaSep1 (parseSymbol && ((colon >> SortParser.parseSort sign) || succeed EXP)) << symbol "<-" || succeed [])
          && f MTAC
          wth BINDING

      fun makeSeq mt (us : (symbol * sort) list) t =
          Syn.into (Syn.TAC_SEQ (mt, us, t))

      fun multitacToTac tm =
        case Syn.out tm of
           Syn.MTAC_ALL t => t
         | _ => makeSeq tm [] (Syn.into Syn.TAC_ID)

      val rec compileScript =
        fn [] => fail "Expected tactic script"
         | [BINDING (_, tac)] => succeed (multitacToTac tac)
         | BINDING (us, tac) :: ts =>
             compileScript ts
               wth makeSeq tac us
    in
      !! (sepEnd1' parseComponent semi
        -- compileScript) wth (fn (t, pos) => Atm (Ast.annotate pos t))
    end

end
