(* 2017/06/24
 * As a note on programming style, the most important or most interesting
 * subgoals should go first, as long as telescopes are well-formed.
 *
 * Rules violating this principle should be updated.
 *)
functor Refiner (Sig : MINI_SIGNATURE) : REFINER =
struct
  (* This is just to get SML/NJ to typecheck the new machine module; unused code doesn't get typechecked otherwise for some reason. *)
  local structure M = RedPrlMachine (Sig) in end

  structure Kit = RefinerKit (Sig)
  structure ComKit = RefinerCompositionKit (Sig)
  structure TypeRules = RefinerTypeRules (Sig)
  structure MiscRules = RefinerMiscRules (Sig)
  open RedPrlAbt Kit ComKit TypeRules MiscRules

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type hyp = Sym.t
  type catjdg = AJ.jdg
  type opid = Sig.opid
  type rule_name = string

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix orelse_ then_ thenl

  structure Hyp =
  struct
    fun Project z _ jdg =
      let
        val _ = RedPrlLog.trace "Hyp.Project"
        val (I, H) >> catjdg = jdg
        val catjdg' = Hyps.lookup z H
      in
        if AJ.eq (catjdg, catjdg') then
          T.empty #> (I, H, Syn.into (Syn.VAR (z, AJ.synthesis catjdg)))
        else
          raise E.error
            [Fpp.text "Hypothesis",
             Fpp.expr @@ Fpp.hsep [TermPrinter.ppSym z, Fpp.Atomic.colon, AJ.pretty catjdg'],
             Fpp.text "does not match goal",
             AJ.pretty catjdg]
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected sequent judgment"]

    fun Rename z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Rename"
        val (I, H) >> catjdg = jdg
        val zjdg = Hyps.lookup z H
        val z' = alpha 0

        val renameIn = VarKit.rename (z', z)
        val renameOut = VarKit.rename (z, z')

        val H' = Hyps.splice H z (Hyps.singleton z' zjdg)
        val H'' = Hyps.modifyAfter z' (AJ.map renameIn) H'

        val (goal, hole) = makeGoal @@ (I, H'') >> AJ.map renameIn catjdg
        val extract = renameOut hole
      in
        |>: goal #> (I, H, extract)
      end

    fun Delete z _ jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Delete"
        val (I, H) >> catjdg = jdg

        fun checkAJ catjdg = 
          let
            val tm = AJ.into catjdg
            val vars = varctx tm
          in
            if Var.Ctx.member vars z then 
              raise E.error [Fpp.text "Cannot delete hypothesis which is mentioned in sequent"]
            else
             ()
          end

        val _ = checkAJ catjdg
        val _ = Hyps.foldr (fn (_, catjdg, _) => (checkAJ catjdg; ())) () H

        val H' = Hyps.remove z H
        val (goal, hole) = makeGoal @@ (I, H') >> catjdg
      in
        |>: goal #> (I, H, hole)
      end
  end

  structure TypeEquality =
  struct
    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.Symmetry"
        val (I, H) >> AJ.EQ_TYPE ((ty1, ty2), l, k) = jdg
        val goal = makeEqType (I, H) ((ty2, ty1), l, k)
      in
        |>: goal #> (I, H, trivial)
      end

    fun FromEqType z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEqType"
        val (I, H) >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val AJ.EQ_TYPE ((a', b'), l', k') = Hyps.lookup z H
        val _ = Assert.alphaEqEither ((a', b'), a)
        val _ = Assert.alphaEqEither ((a', b'), b)
        val _ = Assert.inUsefulUniv (l', k') (l, k)
        val goal = makeEqTypeUnlessSubUniv (I, H) ((a, b), l, k) (l', k')
      in
        |>:? goal #> (I, H, trivial)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEq"
        val (I, H) >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val AJ.EQ (_, (a', l', k')) = Hyps.lookup z H
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
        val _ = Assert.inUsefulUniv (l', k') (l, k)
        val goal = makeTypeUnlessSubUniv (I, H) (a, l, k) (l', k')
      in
        |>:? goal #> (I, H, trivial)
      end

    fun FromTrue z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromTrue"
        val (I, H) >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val AJ.TRUE (a', l', k') = Hyps.lookup z H
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
        val _ = Assert.inUsefulUniv (l', k') (l, k)
        val goal = makeTypeUnlessSubUniv (I, H) (a, l, k) (l', k')
      in
        |>:? goal #> (I, H, trivial)
      end
  end

  structure Truth =
  struct
    fun Witness tm _ jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> AJ.TRUE (ty, l, k) = jdg
        val goal = makeMem (I, H) (tm, (ty, l, k))
      in
        |>: goal #> (I, H, tm)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected truth sequent but got:", RedPrlSequent.pretty jdg]
  end

  structure Term = 
  struct
    fun Exact tm _ jdg = 
      let
        val _ = RedPrlLog.trace "Term.Exact"
        val (I, H) >> AJ.TERM tau = jdg
        val tau' = Abt.sort tm
        val _ = Assert.sortEq (tau, tau')
      in
        T.empty #> (I, H, tm)
      end
  end

  structure Synth =
  struct
    fun Witness ty _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Witness"
        val (I, H) >> AJ.SYNTH (tm, l, k) = jdg
        val goal = makeMem (I, H) (tm, (ty, l, k))
      in
        |>: goal #> (I, H, ty)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromEq"
        val (I, H) >> AJ.SYNTH (tm, l, k) = jdg
        val AJ.EQ ((a, b), (ty, l', k')) = Hyps.lookup z H
        val _ = Assert.alphaEqEither ((a, b), tm)
        val goalKind = makeTypeUnlessSubUniv (I, H) (ty, l, k) (l', k')
      in
        |>:? goalKind #> (I, H, ty)
      end

    fun VarFromTrue _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.VarFromTrue"
        val (I, H) >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val AJ.TRUE (a, l', k') = Hyps.lookup z H
        val goalKind = makeTypeUnlessSubUniv (I, H) (a, l, k) (l', k')
      in
        |>:? goalKind #> (I, H, a)
      end

    val Var = VarFromTrue
  end

  structure Misc =
  struct
    fun MatchOperator _ jdg =
      let
        val _ = RedPrlLog.trace "Misc.MatchOperator"
        val MATCH (th, k, tm, ps, ms) = jdg

        val Abt.$ (th', args) = Abt.out tm
        val true = Abt.O.eq Sym.eq (th, th')

        val (us, xs) \ arg = List.nth (args, k)
        val srho = ListPair.foldrEq (fn (u,p,rho) => Sym.Ctx.insert rho u p) Sym.Ctx.empty (us, ps)
        val vrho = ListPair.foldrEq (fn (x,m,rho) => Var.Ctx.insert rho x m) Var.Ctx.empty (xs, ms)

        val arg' = substEnv (srho, vrho) arg
      in
        Lcf.|> (T.empty, abtToAbs arg')
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH judgment failed to unify"]

    fun ParamSubst _ jdg = 
      let
        val _ = RedPrlLog.trace "Misc.ParamSubst"
        val (I, H) >> AJ.PARAM_SUBST (psi, m, _) = jdg

        fun getSubstitution (rtm, sigma, u) = 
          case Abt.out rtm of
             Abt.$ (O.POLY (O.PARAM_REF (sigma', r)), _) =>
               if sigma = sigma' then
                 (r, u)
               else
                 raise E.error [Fpp.text "ParamSubst: parameter sort mismatch"]
           | _ => raise E.error [Fpp.text "Parameter substitution not yet materialized"]

        val substitutions = List.map getSubstitution psi
        val rho = List.foldl (fn ((r, u), rho) => Sym.Ctx.insert rho u r) Sym.Ctx.empty substitutions
      in
        T.empty #> (I, H, substSymenv rho m)
      end
  end

  structure Equality =
  struct
    fun VarFromTrue _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.VarFromTrue"
        val (I, H) >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val AJ.TRUE (ty', l', k') = Hyps.lookup x H
        val goalTy = makeSubType (I, H) (ty', l', k') (ty, l, k)
      in
        |>:? goalTy #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected variable-equality sequent"]

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.FromEq"
        val (I, H) >> AJ.EQ ((m1, n1), (ty1, l1, k1)) = jdg
        val AJ.EQ ((m0, n0), (ty0, l0, k0)) = Hyps.lookup z H
        val _ = Assert.alphaEqEither ((m0, n0), m1)
        val _ = Assert.alphaEqEither ((m0, n0), n1)
        val goalTy = makeSubType (I, H) (ty0, l0, k0) (ty1, l1, k1)
      in
        |>:? goalTy #> (I, H, trivial)
      end

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val goal = makeEq (I, H) ((n, m), (ty, l, k))
      in
        |>: goal #> (I, H, trivial)
      end

    fun RewriteTrueByEq sel z alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.RewriteTrueByEq"
        val (I, H) >> catjdg = jdg

        val (currentTy, l, k) =
          case Selector.lookup sel (H, catjdg) of
             AJ.TRUE params => params
           | jdg => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "rewrite tactic", AJ.pretty jdg)

        val truncatedH = Selector.truncateFrom sel H
        val AJ.EQ ((m, n), (ty, l', k')) = Hyps.lookup z truncatedH

        val x = alpha 0
        val truncatedHx = truncatedH @> (x, AJ.TRUE (ty, l', k'))
        val (motiveGoal, motiveHole) = makeTerm (I, truncatedHx) O.EXP
        val motiveWfGoal = makeType (I, truncatedHx) (motiveHole, l, k)

        val motiven = substVar (n, x) motiveHole
        val motivem = substVar (m, x) motiveHole

        val (H', catjdg') = Selector.map sel (fn _ => motiven) (H, catjdg)
        val (rewrittenGoal, rewrittenHole) = makeGoal @@ (I, H') >> catjdg'

        (* XXX When sel != O.IN_GOAL, the following subgoal is suboptimal because we already
         * knew `currentTy` is a type. *)
        (* XXX This two types will never be alpha-equivalent, and so we should skip the checking. *)
        val motiveMatchesMainGoal = makeSubType (I, truncatedH) (motivem, l, k) (currentTy, l, k)
      in
        |>: motiveGoal >: rewrittenGoal >: motiveWfGoal >:? motiveMatchesMainGoal
         #> (I, H, rewrittenHole)
      end
  end

  fun Cut catjdg alpha jdg =
    let
      val _ = RedPrlLog.trace "Cut"
      val (I, H) >> catjdg' = jdg
      val z = alpha 0
      val (goal1, hole1) = makeGoal @@ (I, H) >> catjdg
      val (goal2, hole2) = makeGoal @@ (I, H @> (z, catjdg)) >> catjdg'
    in
      |>: goal1 >: goal2 #> (I, H, substVar (hole1, z) hole2)
    end

  fun CutLemma sign opid params alpha jdg = 
    let
      val z = alpha 0
      val (I, H) >> catjdg = jdg

      val {spec, state, ...} = Sig.lookup sign opid
      val Lcf.|> (lemmaSubgoals, _) = state @@ UniversalSpread.bite 1 alpha

      val (I_spec, H_spec) >> specjdg = spec
      val _ = 
        if Hyps.isEmpty H_spec then () else 
          raise E.error [Fpp.text "Lemmas must have a atomic judgment as a conclusion"]

      val lemmaExtract' =
        let
          val subgoalsList = T.foldr (fn (x, jdg, goals) => (x, jdg) :: goals) [] lemmaSubgoals
          val valences = List.map (RedPrlJudgment.sort o #2) subgoalsList
          val arity = (valences, AJ.synthesis specjdg)
          fun argForSubgoal ((x, jdg), vl) = outb @@ Lcf.L.var x vl
        in
          O.POLY (O.CUST (opid, params, SOME arity)) $$ ListPair.mapEq argForSubgoal (subgoalsList, valences)
        end

      val symenv = ListPair.foldlEq (fn ((x, _), r, rho) => Sym.Ctx.insert rho x r) Sym.Ctx.empty (I_spec, List.map #1 params)
      val H' = H @> (z, AJ.map (substSymenv symenv) specjdg)
      val (mainGoal, mainHole) = makeGoal @@ (I, H') >> catjdg
      val extract = substVar (lemmaExtract', z) mainHole
    in
      lemmaSubgoals >: mainGoal #> (I, H, extract)
    end

  fun Exact tm =
    Truth.Witness tm
      orelse_ Synth.Witness tm
      orelse_ Term.Exact tm



  val lookupRule = 
    fn "bool/eqtype" => Bool.EqType
     | "bool/eq/tt" => Bool.EqTT
     | "bool/eq/ff" => Bool.EqFF
     | "bool/eq/if" => Bool.EqElim
     | "wbool/eqtype" => WBool.EqType
     | "wbool/eq/tt" => WBool.EqTT
     | "wbool/eq/ff" => WBool.EqFF
     | "wbool/eq/fcom" => WBool.EqFCom
     | "wbool/eq/wif" => WBool.EqElim
     | "nat/eqtype" => Nat.EqType
     | "nat/eq/zero" => Nat.EqZero
     | "nat/eq/succ" => Nat.EqSucc
     | "nat/eq/nat-rec" => Nat.EqElim
     | "nat/eqtype/nat-rec" => Nat.EqTypeElim
     | "int/eqtype" => Int.EqType
     | "int/eq/zero" => Int.EqZero
     | "int/eq/succ" => Int.EqSucc
     | "int/eq/negsucc" => Int.EqNegSucc
     | "int/eq/int-rec" => Int.EqElim
     | "void/eqtype" => Void.EqType
     | "S1/eqtype" => S1.EqType
     | "S1/eq/base" => S1.EqBase
     | "S1/eq/loop" => S1.EqLoop
     | "S1/eq/fcom" => S1.EqFCom
     | "S1/eq/S1-rec" => S1.EqElim
     | "fun/eqtype" => Fun.EqType
     | "fun/eq/lam" => Fun.Eq
     | "fun/intro" => Fun.True
     | "fun/eq/eta" => Fun.Eta
     | "fun/eq/app" => Fun.EqApp
     | "fun/eqtype/app" => Fun.EqTypeApp
     | "record/eqtype" => Record.EqType
     | "record/eq/tuple" => Record.Eq
     | "record/eq/eta" => Record.Eta
     | "record/eq/proj" => Record.EqProj
     | "record/intro" => Record.True
     | "path/eqtype" => Path.EqType
     | "path/eq/abs" => Path.Eq
     | "path/intro" => Path.True
     | "path/eq/eta" => Path.Eta
     | "path/eq/app" => Path.EqApp
     | "path/eq/app/const" => Path.EqAppConst
     | "eq/eqtype" => InternalizedEquality.EqType
     | "eq/eq/ax" => InternalizedEquality.Eq
     | "eq/intro" => InternalizedEquality.True
     | "eq/eta" => InternalizedEquality.Eta
     | "eq/internalize" => InternalizedEquality.InternalizeEq
     | "fcom/eqtype" => FormalComposition.EqType
     | "fcom/eq/box" => FormalComposition.Eq
     | "fcom/intro" => FormalComposition.True
     | "V/eqtype" => V.EqType
     | "V/eq/uain" => V.Eq
     | "V/intro" => V.True
     | "universe/eqtype" => Universe.EqType
     | "universe/eq" => Universe.Eq
     | "universe/intro" => Universe.True
     | "hcom/eq" => HCom.Eq
     | "hcom/eq/cap" => HCom.EqCapL
     | "hcom/eq/tube" => HCom.EqTubeL

     | r => raise E.error [Fpp.text "No rule registered with name", Fpp.text r]

  structure Computation =
  struct
    open Computation
    fun Reduce sign = SequentReduce sign
    fun ReduceAll sign = SequentReduceAll sign orelse_ MatchRecordReduce sign
  end

  local
    val CatJdgSymmetry : tactic =
      Equality.Symmetry
        orelse_
      TypeEquality.Symmetry

    fun fail err _ _ = E.raiseError err

    fun matchSeq f alpha jdg =
      f jdg alpha jdg

    fun matchSeqSel O.IN_GOAL f = matchSeq
        (fn _ >> catjdg => f catjdg
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "matchSeqSel", Seq.pretty seq))
      | matchSeqSel (O.IN_HYP z) f = matchSeq
        (fn (_, H) >> _ => f (Hyps.lookup z H)
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "matchSeqSel", Seq.pretty seq))

    fun matchHyp z = matchSeqSel (O.IN_HYP z)

    fun canonicity sign =
      Machine.canonicity sign Machine.NOMINAL (Machine.Unfolding.default sign)

    fun AutoElimBasis ty =
      case Syn.out ty of
         Syn.BOOL => Bool.Elim
       | Syn.VOID => Void.Elim
       | Syn.EQUALITY _ => InternalizedEquality.Elim
       | _ => (fn _ => fail @@ E.NOT_APPLICABLE (Fpp.text "AutoElim", TermPrinter.ppTerm ty))

    fun AutoElim sign = NormalizeHypDelegate AutoElimBasis sign

    (* trying to normalize TRUE hypothesis `z` and then run `tac ty z` *)
    and NormalizeHypDelegate tac sign z =
      NormalizeDelegate (fn ty => tac ty z) sign (O.IN_HYP z)

    (* trying to normalize TRUE hypothesis and then run `tac ty` *)
    and NormalizeDelegate tac sign =
      let
        fun go sel = matchSeqSel sel
          (fn AJ.TRUE (ty, _, _) =>
            (case canonicity sign ty of
                Machine.REDEX => Computation.SequentReduce sign [sel] then_ go sel
              | Machine.NEUTRAL (Machine.VAR z') => (AutoElim sign z' then_ go sel) orelse_ tac ty
              | Machine.NEUTRAL (Machine.OPERATOR theta) => Custom.Unfold sign [theta] [sel] then_ go sel
              | _ => tac ty)
            | jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "Normalize", AJ.pretty jdg))
      in
        go
      end

    (* trying to normalize TRUE goal and then run `tac ty` *)
    fun NormalizeGoalDelegate tac sign = NormalizeDelegate tac sign O.IN_GOAL

    fun autoSynthesizableNeu sign m =
      case Syn.out m of
         Syn.VAR _ => true
       | Syn.WIF _ => true
       | Syn.S1_REC _ => true
       | Syn.APP (f, _) => autoSynthesizableNeu sign f
       | Syn.PROJ (_, t) => autoSynthesizableNeu sign t
       | Syn.PATH_APP (l, _) => autoSynthesizableNeu sign l
       | Syn.CUST => true (* XXX should check the signature *)
       | _ => false
  in
    fun SynthFromHyp z = matchHyp z
      (fn AJ.EQ_TYPE _ =>
            Universe.SynthFromEqType z
        | AJ.EQ _ =>
            Synth.FromEq z
              orelse_
            Universe.SynthFromEqAtType z
        | AJ.TRUE _ =>
            Universe.SynthFromTrue z
              orelse_
            InternalizedEquality.SynthFromTrueEq z
              orelse_
            Universe.SynthFromTrueEqAtType z
        | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "SynthFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppSym z]))

    structure Tactical =
    struct
      val NormalizeGoalDelegate = NormalizeGoalDelegate
      val NormalizeHypDelegate = NormalizeHypDelegate
    end

    local
      fun StepEqTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Bool.EqType
         | (Syn.WBOOL, Syn.WBOOL) => WBool.EqType
         | (Syn.NAT, Syn.NAT) => Nat.EqType
         | (Syn.INT, Syn.INT) => Int.EqType
         | (Syn.VOID, Syn.VOID) => Void.EqType
         | (Syn.S1, Syn.S1) => S1.EqType
         | (Syn.FUN _, Syn.FUN _) => Fun.EqType
         | (Syn.RECORD _, Syn.RECORD _) => Record.EqType
         | (Syn.PATH_TY _, Syn.PATH_TY _) => Path.EqType
         | (Syn.EQUALITY _, Syn.EQUALITY _) => InternalizedEquality.EqType
         | (Syn.FCOM _, Syn.FCOM _) => FormalComposition.EqType
         | (Syn.V _, Syn.V _) => V.EqType
         | (Syn.UNIVERSE _, Syn.UNIVERSE _) => Universe.EqType
         | _ => raise E.error [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

      fun StepEqTypeNeuByElim sign tys =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByElim", AJ.pretty @@ AJ.EQ_TYPE (tys, NONE, K.top))

      fun StepEqTypeNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Universe.VarFromTrue
         | (Syn.WIF _, Syn.WIF _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with wif"
         | (Syn.S1_REC _, Syn.S1_REC _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with S1-rec"
         | (Syn.APP (f, _), Syn.APP _) => if autoSynthesizableNeu sign f then Fun.EqTypeApp
                                          else fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", Fpp.text "unresolved synth")
         | (Syn.PROJ _, Syn.PROJ _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with `!`"
         | (Syn.PATH_APP (_, P.VAR _), Syn.PATH_APP (_, P.VAR _)) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with `@`"
         | (Syn.CUST, Syn.CUST) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with custom operators"
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqTypeNeuByUnfold sign tys =
        fn (Machine.METAVAR a, _) => fail @@ E.NOT_APPLICABLE
              (Fpp.text "StepEqTypeNeuByUnfold", TermPrinter.ppMeta a)
         | (_, Machine.METAVAR a) => fail @@ E.NOT_APPLICABLE
              (Fpp.text "StepEqTypeNeuByUnfold", TermPrinter.ppMeta a)
         | (Machine.OPERATOR theta, _) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | (_, Machine.OPERATOR theta) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByUnfold", AJ.pretty @@ AJ.EQ_TYPE (tys, NONE, K.top))

      fun StepEqTypeNeu sign tys blockers =
        StepEqTypeNeuByElim sign tys blockers
          orelse_
        StepEqTypeNeuByStruct sign tys
          orelse_
        StepEqTypeNeuByUnfold sign tys blockers

      fun StepEqTypeNeuExpand sign ty =
        fn Machine.VAR z => AutoElim sign z
         | Machine.OPERATOR theta => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuExpand", TermPrinter.ppTerm ty)

      fun StepEqType sign (ty1, ty2) =
        case (canonicity sign ty1, canonicity sign ty2) of
           (Machine.REDEX, _) => Computation.SequentReduce sign [O.IN_GOAL]
         | (_, Machine.REDEX) => Computation.SequentReduce sign [O.IN_GOAL]
         | (Machine.CANONICAL, Machine.CANONICAL) => StepEqTypeVal (ty1, ty2)
         | (Machine.NEUTRAL blocker1, Machine.NEUTRAL blocker2) => StepEqTypeNeu sign (ty1, ty2) (blocker1, blocker2)
         | (Machine.NEUTRAL blocker, Machine.CANONICAL) => StepEqTypeNeuExpand sign ty1 blocker
         | (Machine.CANONICAL, Machine.NEUTRAL blocker) => CatJdgSymmetry then_ StepEqTypeNeuExpand sign ty2 blocker
         | _ => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "StepEqType", AJ.pretty @@ AJ.EQ_TYPE ((ty1, ty2), NONE, K.top))

      fun StepEqAtTypeVal ty =
        case Syn.out ty of
           Syn.UNIVERSE _ => Universe.Eq
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqAtTypeVal", TermPrinter.ppTerm ty)

      fun StepEqValAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Computation.SequentReduce sign [O.IN_GOAL]
         | Machine.CANONICAL => StepEqAtTypeVal ty
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqValAtType", TermPrinter.ppTerm ty)

      (* equality of canonical forms *)
      fun StepEqVal sign (m, n) ty =
        StepEqValAtType sign ty
          orelse_
        (case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.TT, Syn.TT, Syn.WBOOL) => WBool.EqTT
         | (Syn.FF, Syn.FF, Syn.WBOOL) => WBool.EqFF
         | (Syn.FCOM _, Syn.FCOM _, Syn.WBOOL) => WBool.EqFCom
         | (Syn.TT, Syn.TT, Syn.BOOL) => Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Bool.EqFF
         | (Syn.ZERO, Syn.ZERO, Syn.NAT) => Nat.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.NAT) => Nat.EqSucc
         | (Syn.ZERO, Syn.ZERO, Syn.INT) => Int.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.INT) => Int.EqSucc
         | (Syn.NEGSUCC _, Syn.NEGSUCC _, Syn.INT) => Int.EqNegSucc
         | (Syn.BASE, Syn.BASE, Syn.S1) => S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => S1.EqLoop
         | (Syn.FCOM _, Syn.FCOM _, Syn.S1) => S1.EqFCom
         | (_, _, Syn.FUN _) => Fun.Eq
         | (_, _, Syn.RECORD _) => Record.Eq
         | (_, _, Syn.PATH_TY _) => Path.Eq
         | (_, _, Syn.EQUALITY _) => InternalizedEquality.Eq
         | (_, _, Syn.FCOM _) => FormalComposition.Eq
         | (_, _, Syn.V _) => V.Eq
         | (_, _, Syn.UNIVERSE _) => Universe.Eq
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqVal", AJ.pretty (AJ.EQ ((m, n), (ty, NONE, K.top)))))

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeuAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Computation.SequentReduce sign [O.IN_GOAL]
         | Machine.CANONICAL => StepEqAtTypeVal ty
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuAtType", TermPrinter.ppTerm ty)

      fun StepEqNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Equality.VarFromTrue
         | (Syn.WIF _, Syn.WIF _) => WBool.EqElim
         | (Syn.S1_REC _, Syn.S1_REC _) => S1.EqElim
         | (Syn.APP (f, _), Syn.APP _) => if autoSynthesizableNeu sign f then Fun.EqApp
                                          else fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", Fpp.text "unresolved synth")
         | (Syn.PROJ _, Syn.PROJ _) => Record.EqProj (* XXX should consult autoSynthesizableNeu *)
         | (Syn.PATH_APP (_, P.VAR _), Syn.PATH_APP (_, P.VAR _)) => Path.EqApp (* XXX should consult autoSynthesizableNeu *)
         | (Syn.CUST, Syn.CUST) => Custom.Eq sign (* XXX should consult autoSynthesizableNeu *)
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeuByElim sign (m, n) =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByElim", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeuByUnfold sign (m, n) =
        fn (Machine.METAVAR a, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByUnfold", TermPrinter.ppMeta a)
         | (_, Machine.METAVAR a) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByUnfold", TermPrinter.ppMeta a)
         | (Machine.OPERATOR theta, _) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | (_, Machine.OPERATOR theta) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByUnfold", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeu sign tms blockers ty =
        StepEqNeuAtType sign ty
          orelse_
        StepEqNeuByElim sign tms blockers
          orelse_
        StepEqNeuByStruct sign tms
          orelse_
        StepEqNeuByUnfold sign tms blockers

      fun StepEqNeuExpand sign _ blocker ty =
        StepEqValAtType sign ty
          orelse_
        (case (blocker, Syn.out ty) of
           (Machine.METAVAR a, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuExpand", TermPrinter.ppMeta a)
         | (_, Syn.FUN _) => Fun.Eta
         | (_, Syn.RECORD _) => Record.Eta
         | (_, Syn.PATH_TY _) => Path.Eta
         | (_, Syn.EQUALITY _) => InternalizedEquality.Eta
         | (Machine.VAR z, _) => AutoElim sign z
         | (Machine.OPERATOR theta, _) => Custom.Unfold sign [theta] [O.IN_GOAL])


      structure HCom =
      struct
        open HCom

        val EqCapR = CatJdgSymmetry then_ EqCapL
        val EqTubeR = CatJdgSymmetry then_ EqTubeL
        val AutoEqL = EqCapL orelse_ EqTubeL orelse_ Eq
        val AutoEqR = EqCapR orelse_ EqTubeR orelse_ Eq

        (* Try all the hcom rules.
         * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
        val AutoEqLR =
          EqCapL orelse_ EqCapR orelse_
          EqTubeL orelse_ EqTubeR orelse_
          Eq
      end

      structure Coe =
      struct
       open Coe

       val EqCapR = CatJdgSymmetry then_ EqCapL
       val AutoEqL = EqCapL orelse_ Eq
       val AutoEqR = EqCapR orelse_ Eq
       val AutoEqLR = EqCapL orelse_ EqCapR orelse_ Eq
      end

      fun StepEqKanStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.HCOM _, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.HCOM _, _) => HCom.AutoEqL
         | (_, Syn.HCOM _) => HCom.AutoEqR
         | (Syn.COE _, Syn.COE _) => Coe.AutoEqLR
         | (Syn.COE _, _) => Coe.AutoEqL
         | (_, Syn.COE _) => Coe.AutoEqR
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqKanStructural", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEq sign ((m, n), ty) =
        (* XXX something is missing here!
         * the handling of hcom/coe and `(@ x 1)` in `ty` should be here,
         * between the above and the next lines. *)
        StepEqKanStruct sign (m, n)
          orelse_
        (case (Syn.out m, canonicity sign m, Syn.out n, canonicity sign n) of
           (_, Machine.REDEX, _, _) => Computation.SequentReduce sign [O.IN_GOAL]
         | (_, _, _, Machine.REDEX) => Computation.SequentReduce sign [O.IN_GOAL]
         | (_, Machine.CANONICAL, _, Machine.CANONICAL) => StepEqVal sign (m, n) ty
         | (Syn.PATH_APP (_, P.APP _), _, _, _) => Path.EqAppConst
         | (_, _, Syn.PATH_APP (_, P.APP _), _) => CatJdgSymmetry then_ Path.EqAppConst
         | (_, Machine.NEUTRAL blocker1, _, Machine.NEUTRAL blocker2) => StepEqNeu sign (m, n) (blocker1, blocker2) ty
         | (_, Machine.NEUTRAL blocker, _, Machine.CANONICAL) => StepEqNeuExpand sign m blocker ty
         | (_, Machine.CANONICAL, _, Machine.NEUTRAL blocker) => CatJdgSymmetry then_ StepEqNeuExpand sign n blocker ty
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", AJ.pretty @@ AJ.EQ ((m, n), (ty, NONE, K.top))))

      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.RECORD [] => Record.True (* the unit type *)
         | Syn.EQUALITY _ => InternalizedEquality.True
         | Syn.UNIVERSE _ => Universe.True
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepTrue", TermPrinter.ppTerm ty)

      fun StepSynth sign m =
        case Syn.out m of
           Syn.VAR _ => Synth.Var
         | Syn.WIF _ => WBool.SynthElim
         | Syn.S1_REC _ => S1.SynthElim
         | Syn.APP _ => Fun.SynthApp
         | Syn.PROJ _ => Record.SynthProj
         | Syn.PATH_APP _ => Path.SynthApp
         | Syn.CUST => Custom.Synth sign
         | _ => raise E.error [Fpp.text "Could not find suitable type synthesis rule for", TermPrinter.ppTerm m]

      fun StepSubUniverseNeuExpand sign u =
        fn Machine.VAR z => AutoElim sign z
         | Machine.OPERATOR theta => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepSubUniverseNeuExpand", TermPrinter.ppTerm u)

      fun StepSubUniverse sign u =
        case (Syn.out u, canonicity sign u) of
           (_, Machine.REDEX) => Computation.SequentReduce sign [O.IN_GOAL]
         | (_, Machine.CANONICAL) => Universe.SubUniverse
         | (Syn.PATH_APP (_, P.APP _), _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "SubUniverse with (@ p const)"
         | (_, Machine.NEUTRAL blocker) => StepSubUniverseNeuExpand sign u blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepSubUniverse", TermPrinter.ppTerm u)

      fun StepJdg sign = matchSeq
        (fn _ >> AJ.EQ_TYPE (tys, _, _) => StepEqType sign tys
          | _ >> AJ.EQ ((m, n), (ty, _, _)) => StepEq sign ((m, n), ty)
          | _ >> AJ.TRUE (ty, _, _) => StepTrue sign ty
          | _ >> AJ.SYNTH (m, _, _) => StepSynth sign m
          | _ >> AJ.SUB_UNIVERSE (univ, _, _) => StepSubUniverse sign univ
          | _ >> AJ.PARAM_SUBST _ => Misc.ParamSubst
          | MATCH _ => Misc.MatchOperator
          | MATCH_RECORD _ => Record.MatchRecord orelse_ Computation.MatchRecordReduce sign then_ Record.MatchRecord
          | _ >> jdg => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "AutoStep", AJ.pretty jdg))

      (* favonia:
       * I temporarily disabled the checking before running the rules
       * because everything is subject to change now.
       *)

      fun FromHypDelegate tac = matchSeq
        (fn (_, H) >> _ =>
              Hyps.foldr
                (fn (z, jdg, accum) => tac (z, jdg) orelse_ accum)
                (fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Fpp.text "empty context"))
                H
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))

      val EqTypeFromHyp = FromHypDelegate
        (fn (z, AJ.EQ_TYPE _) => TypeEquality.FromEqType z
          | (z, AJ.EQ _) =>
              TypeEquality.FromEq z
                orelse_
              Universe.EqTypeFromEq z
          | (z, AJ.TRUE _) =>
              TypeEquality.FromTrue z
                orelse_
              InternalizedEquality.TypeFromTrueEqAtType z
                orelse_
              Universe.EqTypeFromTrueEqType z
          | (z, _)  => fail @@ E.NOT_APPLICABLE (Fpp.text "EqTypeFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppSym z]))

      val EqFromHyp = FromHypDelegate
        (fn (z, AJ.EQ _) => Equality.FromEq z
          | (z, AJ.TRUE _) => InternalizedEquality.EqFromTrueEq z
          | (z, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "EqFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppSym z]))

      val StepJdgFromHyp = matchSeq
        (fn _ >> AJ.EQ_TYPE _ => EqTypeFromHyp
          | _ >> AJ.EQ _ => EqFromHyp
          | seq => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))
    in
      fun AutoStep sign alpha jdg = 
        StepJdg sign alpha jdg
          handle exn =>
            StepJdgFromHyp alpha jdg
              handle _ => raise exn
    end

    local
      fun ElimBasis ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.WBOOL => WBool.Elim
         | Syn.NAT => Nat.Elim
         | Syn.INT => Int.Elim
         | Syn.VOID => Void.Elim
         | Syn.S1 => S1.Elim
         | Syn.FUN _ => Fun.Elim
         | Syn.RECORD _ => Record.Elim
         | Syn.PATH_TY _ => Path.Elim
         | Syn.EQUALITY _ => InternalizedEquality.Elim
         | Syn.UNIVERSE _ => Universe.Elim
         | _ => raise E.error [Fpp.text "elim tactic", TermPrinter.ppTerm ty]
    in
      val Elim = NormalizeHypDelegate ElimBasis
    end

    fun RewriteHyp _ sel z = matchHyp z
      (fn AJ.EQ _ => Equality.RewriteTrueByEq sel z
        | AJ.TRUE _ => InternalizedEquality.RewriteTrueByTrue sel z
        | jdg => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "rewrite-hyp tactic", AJ.pretty jdg))

    fun Rewrite _ = InternalizedEquality.RewriteTrue

    val Symmetry : rule = matchSeq
      (fn _ >> AJ.EQ_TYPE _ => TypeEquality.Symmetry
        | _ >> AJ.EQ _ => Equality.Symmetry
        | _ >> AJ.TRUE _ => InternalizedEquality.Symmetry
        | seq => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "internalize tactic", Seq.pretty seq))

  end
end
