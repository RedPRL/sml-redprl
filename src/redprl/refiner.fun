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
  type catjdg = CJ.jdg
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
        if CJ.eq (catjdg, catjdg') then
          T.empty #> (I, H, Syn.into (Syn.VAR (z, CJ.synthesis catjdg)))
        else
          raise E.error
            [Fpp.text "Hypothesis",
             Fpp.expr @@ Fpp.hsep [TermPrinter.ppSym z, Fpp.Atomic.colon, CJ.pretty catjdg'],
             Fpp.text "does not match goal",
             CJ.pretty catjdg]
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
        val H'' = Hyps.modifyAfter z' (CJ.map renameIn) H'

        val (goal, hole) = makeGoal @@ (I, H'') >> CJ.map renameIn catjdg
        val extract = renameOut hole
      in
        |>: goal #> (I, H, extract)
      end

    fun Delete z _ jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Delete"
        val (I, H) >> catjdg = jdg

        fun checkCJ catjdg = 
          let
            val tm = CJ.into catjdg
            val vars = varctx tm
          in
            if Var.Ctx.member vars z then 
              raise E.error [Fpp.text "Cannot delete hypothesis which is mentioned in sequent"]
            else
             ()
          end

        val _ = checkCJ catjdg
        val _ = Hyps.foldr (fn (_, catjdg, _) => (checkCJ catjdg; ())) () H

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
        val (I, H) >> CJ.EQ_TYPE ((ty1, ty2), l, k) = jdg
        val goal = makeEqType (I, H) ((ty2, ty1), l, k)
      in
        |>: goal #> (I, H, trivial)
      end

    fun inUsefulSubUniv (l', k') (l, k) =
      K.greatestMeetComplement' (k, k') <> SOME k orelse
      (Option.isSome l andalso L.P.<= (l', l))

    fun FromEqType z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val CJ.EQ_TYPE ((a', b'), l', k') = Hyps.lookup z H
        val true = inUsefulSubUniv (l', k') (l, k)
        val _ = Assert.alphaEq (a', a)
        val _ = Assert.alphaEq (b', b)
        val goal = makeEqTypeUnlessSubUniv (I, H) ((a, b), l, k) (l', k')
      in
        |>:? goal #> (I, H, trivial)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEq"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val CJ.EQ (_, (a', l', k')) = Hyps.lookup z H
        val true = inUsefulSubUniv (l', k') (l, k)
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
        val goal = makeTypeUnlessSubUniv (I, H) (a, l, k) (l', k')
      in
        |>:? goal #> (I, H, trivial)
      end

    fun FromTrue z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromTrue"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val CJ.TRUE (a', l', k') = Hyps.lookup z H
        val true = inUsefulSubUniv (l', k') (l, k)
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
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
        val (I, H) >> CJ.TRUE (ty, l, k) = jdg
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
        val (I, H) >> CJ.TERM tau = jdg
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
        val (I, H) >> CJ.SYNTH (tm, l, k) = jdg
        val goal = makeMem (I, H) (tm, (ty, l, k))
      in
        |>: goal #> (I, H, ty)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromEq"
        val (I, H) >> CJ.SYNTH (tm, l, k) = jdg
        val CJ.EQ ((a, b), (ty, l', k')) = Hyps.lookup z H
        val goalKind = makeTypeUnlessSubUniv (I, H) (ty, l, k) (l', k')
      in
        if Abt.eq (a, tm) orelse Abt.eq (b, tm) then
          |>:? goalKind #> (I, H, ty)
        else
          raise Fail "Did not match"
      end

    fun VarFromTrue _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.VarFromTrue"
        val (I, H) >> CJ.SYNTH (tm, l, k) = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val CJ.TRUE (a, l', k') = Hyps.lookup z H
        val goalKind = makeTypeUnlessSubUniv (I, H) (a, l, k) (l', k')
      in
        |>:? goalKind #> (I, H, a)
      end

    val Var = VarFromTrue
  end

  (* XXX Maybe we should look up `z` first? *)
  fun SynthFromHyp z =
    Synth.FromEq z orelse_
    Universe.SynthFromEq z orelse_
    Universe.SynthFromTrue z orelse_
    Universe.SynthFromEqType z

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
        val (I, H) >> CJ.PARAM_SUBST (psi, m, _) = jdg

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
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val CJ.TRUE (ty', l', k') = Hyps.lookup x H
        val goalTy = makeSubType (I, H) (ty', l', k') (ty, l, k)
      in
        |>:? goalTy #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected variable-equality sequent"]

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.FromEq"
        val (I, H) >> CJ.EQ ((m1, n1), (ty1, l1, k1)) = jdg
        val CJ.EQ ((m0, n0), (ty0, l0, k0)) = Hyps.lookup z H
        val _ = Assert.alphaEq (m0, m1)
        val _ = Assert.alphaEq (n0, n1)
        val goalTy = makeSubType (I, H) (ty0, l0, k0) (ty1, l1, k1)
      in
        |>:? goalTy #> (I, H, trivial)
      end

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val goal = makeEq (I, H) ((n, m), (ty, l, k))
      in
        |>: goal #> (I, H, trivial)
      end

    fun RewriteTrue z alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.RewriteTrue"
        val (I, H) >> CJ.TRUE (mainGoal, l, k) = jdg
        val CJ.EQ ((m, n), (ty, l', k')) = Hyps.lookup z H

        val x = alpha 0
        val Hx = H @> (x, CJ.TRUE (ty, l', k'))
        val (motiveGoal, motiveHole) = makeTerm (I, Hx) O.EXP
        val motiveWfGoal = makeType (I, Hx) (motiveHole, NONE, K.top)

        val motiven = substVar (n, x) motiveHole
        val motivem = substVar (m, x) motiveHole

        val (rewrittenGoal, rewrittenHole) = makeTrue (I, H) (motiven, l, k)
        val motiveMatchesMainGoal = makeEqTypeIfDifferent (I, H) ((motivem, mainGoal), l, k)
      in
        |>: motiveGoal >: rewrittenGoal >: motiveWfGoal >:? motiveMatchesMainGoal #> (I, H, rewrittenHole)
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
          raise E.error [Fpp.text "Lemmas must have a categorical judgment as a conclusion"]

      val lemmaExtract' =
        let
          val subgoalsList = T.foldr (fn (x, jdg, goals) => (x, jdg) :: goals) [] lemmaSubgoals
          val valences = List.map (RedPrlJudgment.sort o #2) subgoalsList
          val arity = (valences, CJ.synthesis specjdg)
          fun argForSubgoal ((x, jdg), vl) = outb @@ Lcf.L.var x vl
        in
          O.POLY (O.CUST (opid, params, SOME arity)) $$ ListPair.mapEq argForSubgoal (subgoalsList, valences)
        end

      val symenv = ListPair.foldlEq (fn ((x, _), r, rho) => Sym.Ctx.insert rho x r) Sym.Ctx.empty (I_spec, List.map #1 params)
      val H' = H @> (z, CJ.map (substSymenv symenv) specjdg)
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
     | "fcom/eqtype" => FormalComposition.EqType
     | "fcom/eq/box" => FormalComposition.Eq
     | "fcom/intro" => FormalComposition.True
     | "univalence/eqtype" => Univalence.EqType
     | "univalence/eq/uain" => Univalence.Eq
     | "univalence/intro" => Univalence.True
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
      Equality.Symmetry orelse_ TypeEquality.Symmetry

    fun matchGoal f alpha jdg =
      f jdg alpha jdg

    fun matchHyp z f alpha (jdg as (_, H) >> _) =
      f (Hyps.lookup z H) z alpha jdg

    fun canonicity sign =
      Machine.canonicity sign Machine.NOMINAL (Machine.Unfolding.default sign)

    fun fail err _ _ = E.raiseError err

    fun AutoElimBasis ty =
      case Syn.out ty of
         Syn.BOOL => Bool.Elim
       | Syn.VOID => Void.Elim
       | Syn.EQUALITY _ => InternalizedEquality.Elim
       | _ => (fn _ => fail @@ E.NOT_APPLICABLE (Fpp.text "AutoElim", TermPrinter.ppTerm ty))

    fun ElimHypDelegate tac sign z = matchHyp z
      (fn CJ.TRUE (ty, _, _) =>
        (case canonicity sign ty of
            Machine.REDEX => (fn _ => Computation.SequentReduceHyp sign z then_ ElimHypDelegate tac sign z)
          | Machine.NEUTRAL (Machine.VAR z') => (fn _ => AutoElim sign z' then_ ElimHypDelegate tac sign z)
          | Machine.NEUTRAL (Machine.OPERATOR theta) => (fn _ => Custom.UnfoldHyp sign [theta] z then_ ElimHypDelegate tac sign z)
          | Machine.CANONICAL => tac ty
          | _ => (fn _ => fail @@ E.NOT_APPLICABLE (Fpp.text "ElimHypDelegate", TermPrinter.ppTerm ty)))
        | jdg => (fn _ => fail @@ E.NOT_APPLICABLE (Fpp.text "ElimHypDelegate", CJ.pretty jdg)))
    and AutoElim sign = ElimHypDelegate AutoElimBasis sign
  in
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
         | (Syn.UNIVALENCE _, Syn.UNIVALENCE _) => Univalence.EqType
         | (Syn.UNIVERSE _, Syn.UNIVERSE _) => Universe.EqType
         | _ => raise E.error [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]


      (* favonia:
       * I temporarily disabled the checking before trying the rules
       * because everything is moving now.
       *)
      fun EqTypeFromHyp alpha jdg =
        let
          val (_, H) >> CJ.EQ_TYPE _ = jdg
          val try =
            fn CJ.EQ_TYPE _ => TypeEquality.FromEqType
             | CJ.EQ _ => (fn z => TypeEquality.FromEq z orelse_ Universe.EqTypeFromEq z)
             | CJ.TRUE _ => TypeEquality.FromTrue
             | _ => fn z => fail @@ E.NOT_APPLICABLE (Fpp.text "EqTypeFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppSym z])
        in
          (Hyps.foldl
            (fn (z, jdg, tac) => tac orelse_ try jdg z)
            (fail @@ E.NOT_APPLICABLE (Fpp.text "EqTypeFromHyp", Fpp.text "empty context"))
            H)
          alpha jdg
        end

      fun StepEqTypeNeuByElim sign tys =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByElim", CJ.pretty @@ CJ.EQ_TYPE (tys, NONE, K.top))

      fun StepEqTypeNeuByUnfold sign tys =
        fn (Machine.OPERATOR theta, _) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | (_, Machine.OPERATOR theta) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByUnfold", CJ.pretty @@ CJ.EQ_TYPE (tys, NONE, K.top))

      fun StepEqTypeNeu sign tys blockers =
                Universe.VarFromTrue
        orelse_ StepEqTypeNeuByElim sign tys blockers
        orelse_ StepEqTypeNeuByUnfold sign tys blockers

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
         | _ => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "StepEqType", CJ.pretty @@ CJ.EQ_TYPE ((ty1, ty2), NONE, K.top))

      (* favonia:
       * I temporarily disabled the checking before trying the rules
       * because everything is moving now.
       *)
      fun EqFromHyp alpha jdg =
        let
          val (_, H) >> CJ.EQ _ = jdg
          val try =
            fn CJ.EQ _ => Equality.FromEq
             | CJ.TRUE _ => InternalizedEquality.EqFromTrue
             | CJ.EQ_TYPE _ => Universe.EqFromEqType
             | _ => fn z => fail @@ E.NOT_APPLICABLE (Fpp.text "EqFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppSym z])
        in
          (Hyps.foldl
            (fn (z, jdg, tac) => tac orelse_ try jdg z)
            (fail @@ E.NOT_APPLICABLE (Fpp.text "EqFromHyp", Fpp.text "empty context"))
            H)
          alpha jdg
        end

      fun StepEqAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Computation.SequentReduce sign [O.IN_GOAL]
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqAtType", TermPrinter.ppTerm ty)

      (* equality of canonical forms *)
      fun StepEqVal ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
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
         | (_, _, Syn.UNIVALENCE _) => Univalence.Eq
         | (_, _, Syn.UNIVERSE _) => Universe.Eq
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqVal", CJ.pretty (CJ.EQ ((m, n), (ty, NONE, K.top))))

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Equality.VarFromTrue
         | (Syn.WIF _, Syn.WIF _) => WBool.EqElim
         | (Syn.S1_REC _, Syn.S1_REC _) => S1.EqElim
         | (Syn.APP _, Syn.APP _) => Fun.EqApp
         | (Syn.PROJ _, Syn.PROJ _) => Record.EqProj
         | (Syn.PATH_APP (_, P.VAR _), Syn.PATH_APP (_, P.VAR _)) => Path.EqApp
         | (Syn.CUST, Syn.CUST) => Custom.Eq sign
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeuByElim sign (m, n) =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByElim", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeuByUnfold sign (m, n) =
        fn (Machine.OPERATOR theta, _) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | (_, Machine.OPERATOR theta) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByUnfold", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeu sign tms blockers =
        StepEqNeuByElim sign tms blockers orelse_
        StepEqNeuByStruct sign tms orelse_
        StepEqNeuByUnfold sign tms blockers

      fun StepEqNeuExpand sign m blocker ty =
        case (blocker, Syn.out ty) of
           (_, Syn.FUN _) => Fun.Eta
         | (_, Syn.RECORD _) => Record.Eta
         | (_, Syn.PATH_TY _) => Path.Eta
         | (_, Syn.EQUALITY _) => InternalizedEquality.Eta
         | (Machine.VAR z, _) => AutoElim sign z
         | (Machine.OPERATOR theta, _) => Custom.Unfold sign [theta] [O.IN_GOAL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuExpand", CJ.pretty @@ CJ.MEM (m, (ty, NONE, K.top)))


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

      fun StepEqKanStructural sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.HCOM _, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.HCOM _, _) => HCom.AutoEqL
         | (_, Syn.HCOM _) => HCom.AutoEqR
         | (Syn.COE _, Syn.COE _) => Coe.AutoEqLR
         | (Syn.COE _, _) => Coe.AutoEqL
         | (_, Syn.COE _) => Coe.AutoEqR
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqKanStructural", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEq sign ((m, n), ty) =
        StepEqAtType sign ty orelse_
        (* the handling of hcom/coe and `(@ x 1)` in `ty` should be here,
         * between the above and the next lines. *)
        StepEqKanStructural sign (m, n) orelse_
        (case (Syn.out m, canonicity sign m, Syn.out n, canonicity sign n) of
           (_, Machine.REDEX, _, _) => Computation.SequentReduce sign [O.IN_GOAL]
         | (_, _, _, Machine.REDEX) => Computation.SequentReduce sign [O.IN_GOAL]
         | (_, Machine.CANONICAL, _, Machine.CANONICAL) => StepEqVal ((m, n), ty)
         | (Syn.PATH_APP (_, P.APP _), _, _, _) => Path.EqAppConst
         | (_, _, Syn.PATH_APP (_, P.APP _), _) => CatJdgSymmetry then_ Path.EqAppConst
         | (_, Machine.NEUTRAL blocker1, _, Machine.NEUTRAL blocker2) => StepEqNeu sign (m, n) (blocker1, blocker2)
         | (_, Machine.NEUTRAL blocker, _, Machine.CANONICAL) => StepEqNeuExpand sign m blocker ty
         | (_, Machine.CANONICAL, _, Machine.NEUTRAL blocker) => CatJdgSymmetry then_ StepEqNeuExpand sign n blocker ty
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", CJ.pretty @@ CJ.EQ ((m, n), (ty, NONE, K.top))))

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

      fun StepJdg sign = matchGoal
        (fn _ >> CJ.EQ_TYPE (tys, _, _) => StepEqType sign tys
          | _ >> CJ.EQ ((m, n), (ty, _, _)) => StepEq sign ((m, n), ty)
          | _ >> CJ.TRUE (ty, _, _) => StepTrue sign ty
          | _ >> CJ.SYNTH (m, _, _) => StepSynth sign m
          | _ >> CJ.PARAM_SUBST _ => Misc.ParamSubst
          | MATCH _ => Misc.MatchOperator
          | MATCH_RECORD _ => Record.MatchRecord orelse_ Computation.MatchRecordReduce sign then_ Record.MatchRecord
          | _ >> jdg => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "AutoStep", CJ.pretty jdg))

    in
      fun AutoStep sign alpha jdg = 
        StepJdg sign alpha jdg
          handle exn => 
            (EqTypeFromHyp orelse_ EqFromHyp) alpha jdg
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
      val Elim = ElimHypDelegate ElimBasis
    end

    fun Rewrite _ = Equality.RewriteTrue (* todo: rewrite other kinds of goals *)

    fun Internalize _ =
      InternalizedEquality.InternalizeEq orelse_
      Universe.InternalizeEqType

  end
end
