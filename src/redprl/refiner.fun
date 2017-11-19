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
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.rule
  type hyp = Sym.t
  type catjdg = AJ.jdg
  type opid = Sig.opid
  type rule_name = string

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix par orelse_ then_ thenl

  structure Hyp =
  struct
    fun Project z _ jdg =
      let
        val _ = RedPrlLog.trace "Hyp.Project"
        val H >> catjdg = jdg
        val catjdg' = Hyps.lookup H z
      in
        if AJ.eq (catjdg, catjdg') then
          T.empty #> (H, Syn.into (Syn.VAR (z, AJ.synthesis catjdg)))
        else
          raise E.error
            [Fpp.text "Hypothesis",
             Fpp.expr @@ Fpp.hsep [TermPrinter.ppVar z, Fpp.Atomic.colon, AJ.pretty catjdg'],
             Fpp.text "does not match goal",
             AJ.pretty catjdg]
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected sequent judgment"]

    fun Rename z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Rename"
        val H >> catjdg = jdg
        val zjdg = Hyps.lookup H z
        val z' = alpha 0

        val renameIn = VarKit.rename (z', z)
        val renameOut = VarKit.rename (z, z')

        val H' = Hyps.splice H z (Hyps.singleton z' zjdg)
        val H'' = Hyps.modifyAfter z' (AJ.map renameIn) H'

        val (goal, hole) = makeGoal @@ (H'') >> AJ.map renameIn catjdg
        val extract = renameOut hole
      in
        |>: goal #> (H, extract)
      end

    fun Delete z _ jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Delete"
        val H >> catjdg = jdg

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
        val (goal, hole) = makeGoal @@ H' >> catjdg
      in
        |>: goal #> (H, hole)
      end
  end

  structure TypeEquality =
  struct
    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.Symmetry"
        val H >> AJ.EQ_TYPE ((ty1, ty2), l, k) = jdg
        val goal = makeEqType H ((ty2, ty1), l, k)
      in
        |>: goal #> (H, trivial)
      end

    fun FromEqType z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEqType"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val AJ.EQ_TYPE ((a', b'), l', k') = Hyps.lookup H z
        val _ = Assert.alphaEqEither ((a', b'), a)
        val _ = Assert.alphaEqEither ((a', b'), b)
        val _ = Assert.inUsefulUniv (l', k') (l, k)
        val goal = makeEqTypeUnlessSubUniv H ((a, b), l, k) (l', k')
      in
        |>:? goal #> (H, trivial)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEq"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val AJ.EQ (_, (a', l', k')) = Hyps.lookup H z
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
        val _ = Assert.inUsefulUniv (l', k') (l, k)
        val goal = makeTypeUnlessSubUniv H (a, l, k) (l', k')
      in
        |>:? goal #> (H, trivial)
      end

    fun FromTrue z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromTrue"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val AJ.TRUE (a', l', k') = Hyps.lookup H z
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
        val _ = Assert.inUsefulUniv (l', k') (l, k)
        val goal = makeTypeUnlessSubUniv H (a, l, k) (l', k')
      in
        |>:? goal #> (H, trivial)
      end
  end

  structure Truth =
  struct
    fun Witness tm _ jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val goal = makeMem H (tm, (ty, l, k))
      in
        |>: goal #> (H, tm)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected truth sequent but got:", RedPrlSequent.pretty jdg]
  end

  structure Term = 
  struct
    fun Exact tm _ jdg = 
      let
        val _ = RedPrlLog.trace "Term.Exact"
        val H >> AJ.TERM tau = jdg
        val tau' = Abt.sort tm
        val _ = Assert.sortEq (tau, tau')
      in
        T.empty #> (H, tm)
      end
  end

  structure Synth =
  struct
    fun Witness ty _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Witness"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val goal = makeMem H (tm, (ty, l, k))
      in
        |>: goal #> (H, ty)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromEq"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val AJ.EQ ((a, b), (ty, l', k')) = Hyps.lookup H z
        val _ = Assert.alphaEqEither ((a, b), tm)
        val goalKind = makeTypeUnlessSubUniv H (ty, l, k) (l', k')
      in
        |>:? goalKind #> (H, ty)
      end

    fun VarFromTrue _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.VarFromTrue"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val AJ.TRUE (a, l', k') = Hyps.lookup H z
        val goalKind = makeTypeUnlessSubUniv H (a, l, k) (l', k')
      in
        |>:? goalKind #> (H, a)
      end

    val Var = VarFromTrue
  end

  structure Misc =
  struct
    fun MatchOperator _ jdg =
      let
        val _ = RedPrlLog.trace "Misc.MatchOperator"
        val MATCH (th, k, tm, ms) = jdg
        val Abt.$ (th', args) = Abt.out tm
        val true = Abt.O.eq (th, th')

        val xs \ arg = List.nth (args, k)
        val vrho = ListPair.foldrEq (fn (x,m,rho) => Var.Ctx.insert rho x m) Var.Ctx.empty (xs, ms)
        val arg' = substVarenv vrho arg
      in
        Lcf.|> (T.empty, abtToAbs arg')
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH judgment failed to unify"]
  end

  structure Equality =
  struct
    fun VarFromTrue _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.VarFromTrue"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val AJ.TRUE (ty', l', k') = Hyps.lookup H x
        val goalTy = makeSubType H (ty', l', k') (ty, l, k)
      in
        |>:? goalTy #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected variable-equality sequent"]

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.FromEq"
        val H >> AJ.EQ ((m1, n1), (ty1, l1, k1)) = jdg
        val AJ.EQ ((m0, n0), (ty0, l0, k0)) = Hyps.lookup H z
        val _ = Assert.alphaEqEither ((m0, n0), m1)
        val _ = Assert.alphaEqEither ((m0, n0), n1)
        val goalTy = makeSubType H (ty0, l0, k0) (ty1, l1, k1)
      in
        |>:? goalTy #> (H, trivial)
      end

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val goal = makeEq H ((n, m), (ty, l, k))
      in
        |>: goal #> (H, trivial)
      end

    fun RewriteTrueByEq sel z alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.RewriteTrueByEq"
        val H >> catjdg = jdg

        val (currentTy, l, k) =
          case Selector.lookup sel (H, catjdg) of
             AJ.TRUE params => params
           | jdg => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "rewrite tactic", AJ.pretty jdg)

        val truncatedH = Selector.truncateFrom sel H
        val AJ.EQ ((m, n), (ty, l', k')) = Hyps.lookup truncatedH z

        val x = alpha 0
        val truncatedHx = truncatedH @> (x, AJ.TRUE (ty, l', k'))
        val (motiveGoal, motiveHole) = makeTerm (truncatedHx) O.EXP
        val motiveWfGoal = makeType (truncatedHx) (motiveHole, l, k)

        val motiven = substVar (n, x) motiveHole
        val motivem = substVar (m, x) motiveHole

        val (H', catjdg') = Selector.map sel (fn _ => motiven) (H, catjdg)
        val (rewrittenGoal, rewrittenHole) = makeGoal @@ H' >> catjdg'

        (* XXX When sel != O.IN_CONCL, the following subgoal is suboptimal because we already
         * knew `currentTy` is a type. *)
        (* XXX This two types will never be alpha-equivalent, and so we should skip the checking. *)
        val motiveMatchesMainGoal = makeSubType (truncatedH) (motivem, l, k) (currentTy, l, k)
      in
        |>: motiveGoal >: rewrittenGoal >: motiveWfGoal >:? motiveMatchesMainGoal
         #> (H, rewrittenHole)
      end
  end

  fun Cut catjdg alpha jdg =
    let
      val _ = RedPrlLog.trace "Cut"
      val H >> catjdg' = jdg
      val z = alpha 0
      val (goal1, hole1) = makeGoal @@ H >> catjdg
      val (goal2, hole2) = makeGoal @@ (H @> (z, catjdg)) >> catjdg'
    in
      |>: goal1 >: goal2 #> (H, substVar (hole1, z) hole2)
    end

  fun CutLemma sign opid alpha jdg = 
    let
      val z = alpha 0
      val H >> catjdg = jdg

      val {spec, state, ...} = Sig.lookup sign opid
      val Lcf.|> (lemmaSubgoals, _) = state @@ NameSeq.bite 1 alpha

      val H_spec >> specjdg = spec
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
          O.CUST (opid, SOME arity) $$ ListPair.mapEq argForSubgoal (subgoalsList, valences)
        end


      val H' = H @> (z, specjdg)
      val (mainGoal, mainHole) = makeGoal @@ H' >> catjdg
      val extract = substVar (lemmaExtract', z) mainHole
    in
      lemmaSubgoals >: mainGoal #> (H, extract)
    end

  fun Exact tm =
    Lcf.rule o Truth.Witness tm
      orelse_ Lcf.rule o Synth.Witness tm
      orelse_ Lcf.rule o Term.Exact tm



  val lookupRule = 
    fn "bool/eqtype" => Lcf.rule o Bool.EqType
     | "bool/eq/tt" => Lcf.rule o Bool.EqTT
     | "bool/eq/ff" => Lcf.rule o Bool.EqFF
     | "bool/eq/if" => Lcf.rule o Bool.EqElim
     | "wbool/eqtype" => Lcf.rule o WBool.EqType
     | "wbool/eq/tt" => Lcf.rule o WBool.EqTT
     | "wbool/eq/ff" => Lcf.rule o WBool.EqFF
     | "wbool/eq/fcom" => Lcf.rule o WBool.EqFCom
     | "wbool/eq/wif" => Lcf.rule o WBool.EqElim
     | "nat/eqtype" => Lcf.rule o Nat.EqType
     | "nat/eq/zero" => Lcf.rule o Nat.EqZero
     | "nat/eq/succ" => Lcf.rule o Nat.EqSucc
     | "nat/eq/nat-rec" => Lcf.rule o Nat.EqElim
     | "nat/eqtype/nat-rec" => Lcf.rule o Nat.EqTypeElim
     | "int/eqtype" => Lcf.rule o Int.EqType
     | "int/eq/zero" => Lcf.rule o Int.EqZero
     | "int/eq/succ" => Lcf.rule o Int.EqSucc
     | "int/eq/negsucc" => Lcf.rule o Int.EqNegSucc
     | "int/eq/int-rec" => Lcf.rule o Int.EqElim
     | "void/eqtype" => Lcf.rule o Void.EqType
     | "s1/eqtype" => Lcf.rule o S1.EqType
     | "s1/eq/base" => Lcf.rule o S1.EqBase
     | "s1/eq/loop" => Lcf.rule o S1.EqLoop
     | "s1/eq/fcom" => Lcf.rule o S1.EqFCom
     | "s1/eq/s1-rec" => Lcf.rule o S1.EqElim
     | "fun/eqtype" => Lcf.rule o Fun.EqType
     | "fun/eq/lam" => Lcf.rule o Fun.Eq
     | "fun/intro" => Lcf.rule o Fun.True
     | "fun/eq/eta" => Lcf.rule o Fun.Eta
     | "fun/eq/app" => Lcf.rule o Fun.EqApp
     | "fun/eqtype/app" => Lcf.rule o Fun.EqTypeApp
     | "record/eqtype" => Lcf.rule o Record.EqType
     | "record/eq/tuple" => Lcf.rule o Record.Eq
     | "record/eq/eta" => Lcf.rule o Record.Eta
     | "record/eq/proj" => Lcf.rule o Record.EqProj
     | "record/intro" => Lcf.rule o Record.True
     | "path/eqtype" => Lcf.rule o Path.EqType
     | "path/eq/abs" => Lcf.rule o Path.Eq
     | "path/intro" => Lcf.rule o Path.True
     | "path/eq/eta" => Lcf.rule o Path.Eta
     | "path/eq/app" => Lcf.rule o Path.EqApp
     | "path/eq/app/const" => Lcf.rule o Path.EqAppConst
     | "line/eqtype" => Lcf.rule o Line.EqType
     | "line/eq/abs" => Lcf.rule o Line.Eq
     | "line/intro" => Lcf.rule o Line.True
     | "line/eq/eta" => Lcf.rule o Line.Eta
     | "line/eq/app" => Lcf.rule o Line.EqApp
     | "pushout/eqtype" => Lcf.rule o Pushout.EqType
     | "pushout/eq/left" => Lcf.rule o Pushout.EqLeft
     | "pushout/eq/right" => Lcf.rule o Pushout.EqRight
     | "pushout/eq/glue" => Lcf.rule o Pushout.EqGlue
     | "pushout/eq/fcom" => Lcf.rule o Pushout.EqFCom
     | "pushout/eq/pushout-rec" => Lcf.rule o Pushout.EqElim
     | "eq/eqtype" => Lcf.rule o InternalizedEquality.EqType
     | "eq/eq/ax" => Lcf.rule o InternalizedEquality.Eq
     | "eq/intro" => Lcf.rule o InternalizedEquality.True
     | "eq/eta" => Lcf.rule o InternalizedEquality.Eta
     | "eq/internalize" => Lcf.rule o InternalizedEquality.InternalizeEq
     | "fcom/eqtype" => Lcf.rule o FormalComposition.EqType
     | "fcom/eq/box" => Lcf.rule o FormalComposition.Eq
     | "fcom/intro" => Lcf.rule o FormalComposition.True
     | "V/eqtype" => Lcf.rule o V.EqType
     | "V/eq/uain" => Lcf.rule o V.Eq
     | "V/intro" => Lcf.rule o V.True
     | "universe/eqtype" => Lcf.rule o Universe.EqType
     | "universe/eq" => Lcf.rule o Universe.Eq
     | "universe/intro" => Lcf.rule o Universe.True
     | "hcom/eq" => Lcf.rule o HCom.Eq
     | "hcom/eq/cap" => Lcf.rule o HCom.EqCapL
     | "hcom/eq/tube" => Lcf.rule o HCom.EqTubeL
     | "coe/eq" => Lcf.rule o Coe.Eq
     | "coe/eq/cap" => Lcf.rule o Coe.EqCapL

     | r => raise E.error [Fpp.text "No rule registered with name", Fpp.text r]

  structure Computation =
  struct
    open Computation
    fun Reduce sign = SequentReduce sign
    fun ReduceAll sign = Lcf.rule o SequentReduceAll sign orelse_ Lcf.rule o MatchRecordReduce sign
  end

  local
    val CatJdgSymmetry : tactic =
      (Lcf.rule o Equality.Symmetry)
        orelse_
      (Lcf.rule o TypeEquality.Symmetry)

    fun fail err _ _ = Lcf.M.throw (E.errorToExn (NONE, err))

    fun matchGoal f alpha jdg =
      f jdg alpha jdg

    fun matchGoalSel O.IN_CONCL f = matchGoal
        (fn _ >> catjdg => f catjdg
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "matchGoalSel", Seq.pretty seq))
      | matchGoalSel (O.IN_HYP z) f = matchGoal
        (fn H >> _ => f (Hyps.lookup H z)
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "matchGoalSel", Seq.pretty seq))

    fun matchHyp z = matchGoalSel (O.IN_HYP z)

    fun canonicity sign =
      Machine.canonicity sign Machine.NOMINAL (Machine.Unfolding.default sign)

    fun AutoElimBasis ty z : tactic =
      case Syn.out ty of
         Syn.BOOL => Lcf.rule o Bool.Elim z
       | Syn.VOID => Lcf.rule o Void.Elim z
       | Syn.EQUALITY _ => Lcf.rule o InternalizedEquality.Elim z
       | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "AutoElim", TermPrinter.ppTerm ty)

    fun AutoElim sign = NormalizeHypDelegate AutoElimBasis sign

    (* trying to normalize TRUE hypothesis `z` and then run `tac ty z` *)
    and NormalizeHypDelegate (tac : abt -> hyp -> tactic) sign z : tactic =
      NormalizeDelegate (fn ty => tac ty z) sign (O.IN_HYP z)

    (* trying to normalize TRUE hypothesis and then run `tac ty` *)
    and NormalizeDelegate (tac : abt -> tactic) sign =
      let
        fun go sel = matchGoalSel sel
          (fn AJ.TRUE (ty, _, _) =>
            (case canonicity sign ty of
                Machine.REDEX => Lcf.rule o Computation.SequentReduce sign [sel] then_ go sel
              | Machine.NEUTRAL (Machine.VAR z') => (AutoElim sign z' then_ go sel) orelse_ tac ty
              | Machine.NEUTRAL (Machine.OPERATOR theta) => (Lcf.rule o Custom.Unfold sign [theta] [sel]) then_ go sel
              | _ => tac ty)
            | jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "Normalize", AJ.pretty jdg))
      in
        go
      end

    (* trying to normalize TRUE goal and then run `tac ty` *)
    fun NormalizeGoalDelegate tac sign = NormalizeDelegate tac sign O.IN_CONCL

    fun autoSynthesizableNeu sign m =
      case Syn.out m of
         Syn.VAR _ => true
       | Syn.WIF _ => true
       | Syn.S1_REC _ => true
       | Syn.APP (f, _) => autoSynthesizableNeu sign f
       | Syn.PROJ (_, t) => autoSynthesizableNeu sign t
       | Syn.DIM_APP (l, _) => autoSynthesizableNeu sign l
       | Syn.PUSHOUT_REC _ => true
       | Syn.CUST => true (* XXX should check the signature *)
       | _ => false
  in
    fun SynthFromHyp z = matchHyp z
      (fn AJ.EQ_TYPE _ =>
           Lcf.rule o Universe.SynthFromEqType z
        | AJ.EQ _ =>
           Lcf.rule o Synth.FromEq z
              orelse_
           Lcf.rule o Universe.SynthFromEqAtType z
        | AJ.TRUE _ =>
            Lcf.rule o Universe.SynthFromTrue z
              orelse_
            Lcf.rule o InternalizedEquality.SynthFromTrueEq z
              orelse_
            Lcf.rule o Universe.SynthFromTrueEqAtType z
        | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "SynthFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

    structure Tactical =
    struct
      val NormalizeGoalDelegate = NormalizeGoalDelegate
      val NormalizeHypDelegate = NormalizeHypDelegate
    end

    local
      fun StepEqTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Lcf.rule o Bool.EqType
         | (Syn.WBOOL, Syn.WBOOL) => Lcf.rule o WBool.EqType
         | (Syn.NAT, Syn.NAT) => Lcf.rule o Nat.EqType
         | (Syn.INT, Syn.INT) => Lcf.rule o Int.EqType
         | (Syn.VOID, Syn.VOID) => Lcf.rule o Void.EqType
         | (Syn.S1, Syn.S1) => Lcf.rule o S1.EqType
         | (Syn.FUN _, Syn.FUN _) => Lcf.rule o Fun.EqType
         | (Syn.RECORD _, Syn.RECORD _) => Lcf.rule o Record.EqType
         | (Syn.PATH _, Syn.PATH _) => Lcf.rule o Path.EqType
         | (Syn.LINE _, Syn.LINE _) => Lcf.rule o Line.EqType
         | (Syn.PUSHOUT _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqType
         | (Syn.EQUALITY _, Syn.EQUALITY _) => Lcf.rule o InternalizedEquality.EqType
         | (Syn.FCOM _, Syn.FCOM _) => Lcf.rule o FormalComposition.EqType
         | (Syn.V _, Syn.V _) => Lcf.rule o V.EqType
         | (Syn.UNIVERSE _, Syn.UNIVERSE _) => Lcf.rule o Universe.EqType
         | _ => fail @@ E.GENERIC [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

      fun StepEqTypeNeuByElim sign tys =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByElim", AJ.pretty @@ AJ.EQ_TYPE (tys, NONE, K.top))

      fun StepEqTypeNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Lcf.rule o Universe.VarFromTrue
         | (Syn.WIF _, Syn.WIF _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with wif"
         | (Syn.S1_REC _, Syn.S1_REC _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with S1-rec"
         | (Syn.APP (f, _), Syn.APP _) => if autoSynthesizableNeu sign f then Lcf.rule o Fun.EqTypeApp
                                          else fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", Fpp.text "unresolved synth")
         | (Syn.PROJ _, Syn.PROJ _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with `!`"
         | (Syn.DIM_APP (_, _), Syn.DIM_APP (_, _)) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with `@`" (* pattern used to have a var for the dimension; needed? *)
         | (Syn.PUSHOUT_REC _, Syn.PUSHOUT_REC _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with pushout-rec"
         | (Syn.CUST, Syn.CUST) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "EqType with custom operators"
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqTypeNeuByUnfold sign tys =
        fn (Machine.METAVAR a, _) => fail @@ E.NOT_APPLICABLE
              (Fpp.text "StepEqTypeNeuByUnfold", TermPrinter.ppMeta a)
         | (_, Machine.METAVAR a) => fail @@ E.NOT_APPLICABLE
              (Fpp.text "StepEqTypeNeuByUnfold", TermPrinter.ppMeta a)
         | (Machine.OPERATOR theta, _) => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
         | (_, Machine.OPERATOR theta) => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByUnfold", AJ.pretty @@ AJ.EQ_TYPE (tys, NONE, K.top))

      fun StepEqTypeNeu sign tys blockers =
        StepEqTypeNeuByElim sign tys blockers
          orelse_
        StepEqTypeNeuByStruct sign tys
          orelse_
        StepEqTypeNeuByUnfold sign tys blockers

      fun StepEqTypeNeuExpand sign ty =
        fn Machine.VAR z => AutoElim sign z
         | Machine.OPERATOR theta => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuExpand", TermPrinter.ppTerm ty)

      fun StepEqType sign (ty1, ty2) =
        (Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]) then_ 
        (case (canonicity sign ty1, canonicity sign ty2) of
           (Machine.REDEX, _) => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | (_, Machine.REDEX) => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | (Machine.CANONICAL, Machine.CANONICAL) => StepEqTypeVal (ty1, ty2)
         | (Machine.NEUTRAL blocker1, Machine.NEUTRAL blocker2) => StepEqTypeNeu sign (ty1, ty2) (blocker1, blocker2)
         | (Machine.NEUTRAL blocker, Machine.CANONICAL) => StepEqTypeNeuExpand sign ty1 blocker
         | (Machine.CANONICAL, Machine.NEUTRAL blocker) => CatJdgSymmetry then_ StepEqTypeNeuExpand sign ty2 blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqType", AJ.pretty @@ AJ.EQ_TYPE ((ty1, ty2), NONE, K.top)))

      fun StepEqAtTypeVal ty =
        case Syn.out ty of
           Syn.UNIVERSE _ => Lcf.rule o Universe.Eq
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqAtTypeVal", TermPrinter.ppTerm ty)

      fun StepEqValAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | Machine.CANONICAL => StepEqAtTypeVal ty
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqValAtType", TermPrinter.ppTerm ty)

      (* equality of canonical forms *)
      fun StepEqVal sign (m, n) ty =
        StepEqValAtType sign ty
          orelse_
        (case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.TT, Syn.TT, Syn.WBOOL) => Lcf.rule o WBool.EqTT
         | (Syn.FF, Syn.FF, Syn.WBOOL) => Lcf.rule o WBool.EqFF
         | (Syn.FCOM _, Syn.FCOM _, Syn.WBOOL) => Lcf.rule o WBool.EqFCom
         | (Syn.TT, Syn.TT, Syn.BOOL) => Lcf.rule o Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Lcf.rule o Bool.EqFF
         | (Syn.ZERO, Syn.ZERO, Syn.NAT) => Lcf.rule o Nat.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.NAT) => Lcf.rule o Nat.EqSucc
         | (Syn.ZERO, Syn.ZERO, Syn.INT) => Lcf.rule o Int.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.INT) => Lcf.rule o Int.EqSucc
         | (Syn.NEGSUCC _, Syn.NEGSUCC _, Syn.INT) => Lcf.rule o Int.EqNegSucc
         | (Syn.BASE, Syn.BASE, Syn.S1) => Lcf.rule o S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => Lcf.rule o S1.EqLoop
         | (Syn.FCOM _, Syn.FCOM _, Syn.S1) => Lcf.rule o S1.EqFCom
         | (_, _, Syn.FUN _) => Lcf.rule o Fun.Eq
         | (_, _, Syn.RECORD _) => Lcf.rule o Record.Eq
         | (_, _, Syn.PATH _) => Lcf.rule o Path.Eq
         | (_, _, Syn.LINE _) => Lcf.rule o Line.Eq
         | (Syn.LEFT _, Syn.LEFT _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqLeft
         | (Syn.RIGHT _, Syn.RIGHT _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqRight
         | (Syn.GLUE _, Syn.GLUE _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqGlue
         | (Syn.FCOM _, Syn.FCOM _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqFCom
         | (_, _, Syn.EQUALITY _) => Lcf.rule o InternalizedEquality.Eq
         | (_, _, Syn.FCOM _) => Lcf.rule o FormalComposition.Eq
         | (_, _, Syn.V _) => Lcf.rule o V.Eq
         | (_, _, Syn.UNIVERSE _) => Lcf.rule o Universe.Eq
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqVal", AJ.pretty (AJ.EQ ((m, n), (ty, NONE, K.top)))))

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeuAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | Machine.CANONICAL => StepEqAtTypeVal ty
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuAtType", TermPrinter.ppTerm ty)

      fun StepEqNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Lcf.rule o Equality.VarFromTrue
         | (Syn.WIF _, Syn.WIF _) => Lcf.rule o WBool.EqElim
         | (Syn.S1_REC _, Syn.S1_REC _) => Lcf.rule o S1.EqElim
         | (Syn.APP (f, _), Syn.APP _) => if autoSynthesizableNeu sign f then Lcf.rule o Fun.EqApp
                                          else fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", Fpp.text "unresolved synth")
         | (Syn.PROJ _, Syn.PROJ _) => Lcf.rule o Record.EqProj (* XXX should consult autoSynthesizableNeu *)
         | (Syn.DIM_APP (_, r1), Syn.DIM_APP (_, r2)) =>
           (case (Abt.out r1, Abt.out r2) of 
               (`_, `_) => Lcf.rule o Path.EqApp
             | _ =>  fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n]))
              (* XXX should consult autoSynthesizableNeu *)
         | (Syn.PUSHOUT_REC _, Syn.PUSHOUT_REC _) => Lcf.rule o Pushout.EqElim
         | (Syn.CUST, Syn.CUST) => Lcf.rule o Custom.Eq sign (* XXX should consult autoSynthesizableNeu *)
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeuByElim sign (m, n) =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByElim", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeuByUnfold sign (m, n) =
        fn (Machine.METAVAR a, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByUnfold", TermPrinter.ppMeta a)
         | (_, Machine.METAVAR a) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByUnfold", TermPrinter.ppMeta a)
         | (Machine.OPERATOR theta, _) => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
         | (_, Machine.OPERATOR theta) => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
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
           (_, Syn.FUN _) => Lcf.rule o Fun.Eta
         | (_, Syn.RECORD _) => Lcf.rule o Record.Eta
         | (_, Syn.PATH _) => Lcf.rule o Path.Eta
         | (_, Syn.LINE _) => Lcf.rule o Line.Eta
         | (_, Syn.EQUALITY _) => Lcf.rule o InternalizedEquality.Eta
         | (Machine.VAR z, _) => AutoElim sign z
         | (Machine.OPERATOR theta, _) => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL])


      structure HCom =
      struct
        open HCom

        val EqCapR = CatJdgSymmetry then_ Lcf.rule o EqCapL
        val EqTubeR = CatJdgSymmetry then_ Lcf.rule o EqTubeL
        val AutoEqL = Lcf.rule o EqCapL orelse_ Lcf.rule o EqTubeL orelse_  Lcf.rule o Eq
        val AutoEqR = EqCapR orelse_ EqTubeR orelse_ Lcf.rule o Eq

        (* Try all the hcom rules.
         * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
        val AutoEqLR =
          Lcf.rule o EqCapL orelse_ EqCapR orelse_
          Lcf.rule o EqTubeL orelse_ EqTubeR orelse_
          Lcf.rule o Eq
      end

      structure Coe =
      struct
       open Coe

       val EqCapR = CatJdgSymmetry then_ Lcf.rule o EqCapL
       val AutoEqL = Lcf.rule o EqCapL orelse_ Lcf.rule o Eq
       val AutoEqR = EqCapR orelse_ Lcf.rule o Eq
       val AutoEqLR = Lcf.rule o EqCapL orelse_ EqCapR orelse_ Lcf.rule o Eq
      end

      fun ProgressCompute sign = 
        Lcf.progress o (Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL])
      
      fun ComputeBefore sign tac =
        (ProgressCompute sign then_ tac) par tac

      fun StepEqKanStruct sign (m, n) =
        ComputeBefore sign
        (case (Syn.out m, Syn.out n) of
           (Syn.HCOM _, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.HCOM _, _) => HCom.AutoEqL
         | (_, Syn.HCOM _) => HCom.AutoEqR
         | (Syn.COE _, Syn.COE _) => Coe.AutoEqLR
         | (Syn.COE _, _) => Coe.AutoEqL
         | (_, Syn.COE _) => Coe.AutoEqR
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqKanStructural", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n]))

      (* This is really ugly; feel free to refactor, sorry. Wish we had 'backtracking case statements' in SML. *)
      fun StepEqAux sign ((m, n), ty) kont = 
        case (Syn.out m, canonicity sign m, Syn.out n, canonicity sign n) of
           (_, Machine.REDEX, _, _) => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | (_, _, _, Machine.REDEX) => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | (_, Machine.CANONICAL, _, Machine.CANONICAL) => StepEqVal sign (m, n) ty
         | (Syn.DIM_APP (_, r), _, _, _) =>
           (case Abt.out r of 
              `_ => kont ((m, n), ty)
             | _ => Lcf.rule o Path.EqAppConst par Lcf.rule o Line.EqApp)
         | (_, _, Syn.DIM_APP (_, r), _) =>
           (case Abt.out r of 
              `_ => kont ((m, n), ty)
             | _ => CatJdgSymmetry then_ (Lcf.rule o Path.EqAppConst par Lcf.rule o Line.EqApp))
         | _ => kont ((m, n), ty)

      fun StepEq sign ((m, n), ty) =
        (* XXX something is missing here!
         * the handling of hcom/coe and `(@ x 1)` in `ty` should be here,
         * between the above and the next lines. *)
        StepEqKanStruct sign (m, n)
          orelse_
        StepEqAux sign ((m, n), ty) (fn ((m, n), ty) => 
          case (Syn.out m, canonicity sign m, Syn.out n, canonicity sign n) of
             (_, Machine.NEUTRAL blocker1, _, Machine.NEUTRAL blocker2) => StepEqNeu sign (m, n) (blocker1, blocker2) ty
           | (_, Machine.NEUTRAL blocker, _, Machine.CANONICAL) => StepEqNeuExpand sign m blocker ty
           | (_, Machine.CANONICAL, _, Machine.NEUTRAL blocker) => CatJdgSymmetry then_ StepEqNeuExpand sign n blocker ty
           | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", AJ.pretty @@ AJ.EQ ((m, n), (ty, NONE, K.top))))

      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.RECORD [] => Lcf.rule o Record.True (* the unit type *)
         | Syn.EQUALITY _ => Lcf.rule o InternalizedEquality.True
         | Syn.UNIVERSE _ => Lcf.rule o Universe.True
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepTrue", TermPrinter.ppTerm ty)

      fun StepSynth sign m =
        case Syn.out m of
           Syn.VAR _ => Lcf.rule o Synth.Var
         | Syn.WIF _ => Lcf.rule o WBool.SynthElim
         | Syn.S1_REC _ => Lcf.rule o S1.SynthElim
         | Syn.APP _ => Lcf.rule o Fun.SynthApp
         | Syn.PROJ _ => Lcf.rule o Record.SynthProj
         | Syn.DIM_APP _ => Lcf.rule o Path.SynthApp par Lcf.rule o Line.SynthApp
         | Syn.PUSHOUT_REC _ => Lcf.rule o Pushout.SynthElim
         | Syn.CUST => Lcf.rule o Custom.Synth sign
         | _ => fail @@ E.GENERIC [Fpp.text "Could not find suitable type synthesis rule for", TermPrinter.ppTerm m]

      fun StepSubUniverseNeuExpand sign u =
        fn Machine.VAR z => AutoElim sign z
         | Machine.OPERATOR theta => Lcf.rule o Custom.Unfold sign [theta] [O.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepSubUniverseNeuExpand", TermPrinter.ppTerm u)

      fun StepSubUniverse sign u =
        case (Syn.out u, canonicity sign u) of
           (_, Machine.REDEX) => Lcf.rule o Computation.SequentReduce sign [O.IN_CONCL]
         | (_, Machine.CANONICAL) => Lcf.rule o Universe.SubUniverse
         | (Syn.DIM_APP (_, r), _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "SubUniverse with (@ p r)"
         | (_, Machine.NEUTRAL blocker) => StepSubUniverseNeuExpand sign u blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepSubUniverse", TermPrinter.ppTerm u)

      fun StepJdg sign = matchGoal
        (fn _ >> AJ.EQ_TYPE (tys, _, _) => StepEqType sign tys
          | _ >> AJ.EQ ((m, n), (ty, _, _)) => StepEq sign ((m, n), ty)
          | _ >> AJ.TRUE (ty, _, _) => StepTrue sign ty
          | _ >> AJ.SYNTH (m, _, _) => StepSynth sign m
          | _ >> AJ.SUB_UNIVERSE (univ, _, _) => StepSubUniverse sign univ
          | MATCH _ => Lcf.rule o Misc.MatchOperator
          | MATCH_RECORD _ => Lcf.rule o Record.MatchRecord orelse_ Lcf.rule o Computation.MatchRecordReduce sign then_ Lcf.rule o Record.MatchRecord
          | _ >> jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "AutoStep", AJ.pretty jdg))

      (* favonia:
       * I temporarily disabled the checking before running the rules
       * because everything is subject to change now.
       *)

      fun FromHypDelegate tac = matchGoal
        (fn H >> _ =>
              Hyps.foldr
                (fn (z, jdg, accum) => tac (z, jdg) orelse_ accum)
                (fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Fpp.text "empty context"))
                H
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))

      val EqTypeFromHyp = FromHypDelegate
        (fn (z, AJ.EQ_TYPE _) => Lcf.rule o TypeEquality.FromEqType z
          | (z, AJ.EQ _) =>
              Lcf.rule o TypeEquality.FromEq z
                orelse_
              Lcf.rule o Universe.EqTypeFromEq z
          | (z, AJ.TRUE _) =>
              Lcf.rule o TypeEquality.FromTrue z
                orelse_
              Lcf.rule o InternalizedEquality.TypeFromTrueEqAtType z
                orelse_
              Lcf.rule o Universe.EqTypeFromTrueEqType z
          | (z, _)  => fail @@ E.NOT_APPLICABLE (Fpp.text "EqTypeFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

      val EqFromHyp = FromHypDelegate
        (fn (z, AJ.EQ _) => Lcf.rule o Equality.FromEq z
          | (z, AJ.TRUE _) => Lcf.rule o InternalizedEquality.EqFromTrueEq z
          | (z, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "EqFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

      val StepJdgFromHyp = matchGoal
        (fn _ >> AJ.EQ_TYPE _ => EqTypeFromHyp
          | _ >> AJ.EQ _ => EqFromHyp
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))
    in
      fun AutoStep sign =
        StepJdg sign
          orelse_
            StepJdgFromHyp
    end

    local
      fun ElimBasis ty z : tactic = 
        case Syn.out ty of
           Syn.BOOL => Lcf.rule o Bool.Elim z
         | Syn.WBOOL => Lcf.rule o WBool.Elim z
         | Syn.NAT => Lcf.rule o Nat.Elim z
         | Syn.INT => Lcf.rule o Int.Elim z 
         | Syn.VOID => Lcf.rule o Void.Elim z
         | Syn.S1 => Lcf.rule o S1.Elim z
         | Syn.FUN _ => Lcf.rule o Fun.Elim z
         | Syn.RECORD _ => Lcf.rule o Record.Elim z
         | Syn.PATH _ => Lcf.rule o Path.Elim z
         | Syn.LINE _ => Lcf.rule o Line.Elim z
         | Syn.PUSHOUT _ => Lcf.rule o Pushout.Elim z
         | Syn.EQUALITY _ => Lcf.rule o InternalizedEquality.Elim z
         | Syn.UNIVERSE _ => Universe.Elim z
         | _ => fail @@ E.GENERIC [Fpp.text "elim tactic", TermPrinter.ppTerm ty]
    in
      val Elim = NormalizeHypDelegate ElimBasis
    end

    fun RewriteHyp _ sel z = matchHyp z
      (fn AJ.EQ _ => Lcf.rule o Equality.RewriteTrueByEq sel z
        | AJ.TRUE _ => Lcf.rule o InternalizedEquality.RewriteTrueByTrue sel z
        | jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "rewrite-hyp tactic", AJ.pretty jdg))

    fun Rewrite _ = InternalizedEquality.RewriteTrue

    val Symmetry : tactic = matchGoal
      (fn _ >> AJ.EQ_TYPE _ => Lcf.rule o TypeEquality.Symmetry
        | _ >> AJ.EQ _ => Lcf.rule o Equality.Symmetry
        | _ >> AJ.TRUE _ => Lcf.rule o InternalizedEquality.Symmetry
        | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "internalize tactic", Seq.pretty seq))

    fun Inversion z : tactic = Lcf.rule o Record.EqInv z
  end
end
