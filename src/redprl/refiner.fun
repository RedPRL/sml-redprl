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
  type ajdg = AJ.jdg
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
        val tr = ["Hyp.Project"]
        val H >> ajdg = jdg
        val ajdg' = Hyps.lookup H z
      in
        if AJ.eq (ajdg, ajdg') then
          T.empty #> (H, Syn.into (Syn.VAR (z, AJ.synthesis ajdg)))
        else
          raise E.error
            [Fpp.text "Hypothesis",
             Fpp.expr @@ Fpp.hsep [TermPrinter.ppVar z, Fpp.Atomic.colon, AJ.pretty ajdg'],
             Fpp.text "does not match goal",
             AJ.pretty ajdg]
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected sequent judgment"]

    fun Rename z alpha jdg =
      let
        val tr = ["Hyp.Rename"]
        val H >> ajdg = jdg
        val zjdg = Hyps.lookup H z
        val z' = alpha 0

        val renameIn = VarKit.rename (z', z)
        val renameOut = VarKit.rename (z, z')

        val H' = Hyps.splice H z (Hyps.singleton z' zjdg)
        val H'' = Hyps.modifyAfter z' (AJ.map renameIn) H'

        val (goal, hole) = makeGoal tr @@ (H'') >> AJ.map renameIn ajdg
        val extract = renameOut hole
      in
        |>: goal #> (H, extract)
      end

    fun Delete z _ jdg =
      let
        val tr = ["Hyp.Delete"]
        val H >> ajdg = jdg

        fun checkAJ ajdg =
          let
            val tm = AJ.into ajdg
            val vars = varctx tm
          in
            if Var.Ctx.member vars z then
              raise E.error [Fpp.text "Cannot delete hypothesis which is mentioned in sequent"]
            else
             ()
          end

        val _ = checkAJ ajdg
        val _ = Hyps.foldr (fn (_, ajdg, _) => (checkAJ ajdg; ())) () H

        val H' = Hyps.remove z H
        val (goal, hole) = makeGoal tr @@ H' >> ajdg
      in
        |>: goal #> (H, hole)
      end
  end

  structure TypeEquality =
  struct
    fun Symmetry _ jdg =
      let
        val tr = ["TypeEquality.Symmetry"]
        val H >> AJ.EQ_TYPE ((ty1, ty2), k) = jdg
        val goal = makeEqType tr H ((ty2, ty1), k)
      in
        |>: goal #> (H, axiom)
      end

    (* this is for non-deterministic search *)
    fun NondetFromEqType z _ jdg =
      let
        val tr = ["TypeEquality.NondetFromEqType"]
        val H >> AJ.EQ_TYPE ((a, b), k) = jdg
        val AJ.EQ_TYPE ((a', b'), k') = Hyps.lookup H z
        val _ = Assert.alphaEqEither ((a', b'), a)
        val _ = Assert.alphaEqEither ((a', b'), b)
        val _ = Assert.inUsefulUnivOmega (k', k)
        val goal = makeEqTypeUnlessSubUniv tr H ((a, b), k) k'
      in
        |>:? goal #> (H, axiom)
      end

    (* this is for non-deterministic search *)
    fun NondetFromTrue z _ jdg =
      let
        val tr = ["TypeEquality.NondetFromTrue"]
        val H >> AJ.EQ_TYPE ((a, b), k) = jdg
        val AJ.TRUE a' = Hyps.lookup H z
        val _ = Assert.alphaEq (a, b)
        val _ = Assert.alphaEq (a', a)
        val _ = Assert.kindLeq (K.top, k)
      in
        T.empty #> (H, axiom)
      end
  end

  structure SubType =
  struct
    fun Eq _ jdg =
      let
        val tr = ["SubType.Eq"]
        val H >> AJ.SUB_TYPE (a, b) = jdg
        val goal = makeEqType tr H ((a, b), K.top)
      in
        |>: goal #> (H, axiom)
      end
  end

  structure True =
  struct
    fun Witness tm _ jdg =
      let
        val tr = ["True.Witness"]
        val H >> AJ.TRUE ty = jdg
        val goal = makeMem tr H (tm, ty)
      in
        |>: goal #> (H, tm)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected truth sequent but got:", Sequent.pretty jdg]
  end

  structure Term =
  struct
    fun Exact tm _ jdg =
      let
        val tr = ["Term.Exact"]
        val H >> AJ.TERM tau = jdg
        val tau' = Abt.sort tm
        val _ = Assert.sortEq (tau, tau')
      in
        T.empty #> (H, tm)
      end
  end

  structure Synth =
  struct
    infix $ \

    fun General sign _ =
      let
        val tr = ["Synth.General"]

        fun eval sign = 
          Machine.eval sign Machine.STABLE Machine.Unfolding.always

        fun synthNeutral H =
          fn `x =>
             let
               val AJ.TRUE ty = Hyps.lookup H x
             in
               (T.empty, ty)
             end

           | O.CUST (opid, _) $ args =>
             let
               val AJ.TRUE ty = Sig.theoremSpec sign opid args
             in
               (T.empty, ty)
             end

           | O.APP $ [_ \ m1, _ \ m2] =>
             let
               val (psi, funty) = synthTerm H m1
               val Syn.FUN (dom, x, cod) = Syn.out @@ eval sign funty
               val memGoal = makeMem tr H (m2, dom)
             in
               (psi >: memGoal, substVar (m2, x) cod)
             end

           | O.DIM_APP $ [_ \ m, _ \ r] => 
             let
               val (psi, ty) = synthTerm H m
             in
               case Syn.out @@ eval sign ty of
                  Syn.PATH ((x, a), _, _) =>
                  (psi, substVar (r, x) a)

                | Syn.LINE (x, a) =>
                  (psi, substVar (r, x) a)

                | _ => raise Fail "synthNeutral"
             end

           | O.S1_REC $ [[x] \ cx, _ \ m, _ \ b, [u] \ l] =>
             let
               val goalMotive = makeType tr (H @> (x, AJ.TRUE @@ Syn.into Syn.S1)) (cx, RedPrlKind.STABLE)
               val goalS1 = makeMem tr H (m, Syn.into Syn.S1)
               val goalBase = makeMem tr H (b, substVar (Syn.into Syn.BASE, x) cx)
               val goalLoop = makeMem tr (H @> (u, AJ.TERM O.DIM)) (l, substVar (Syn.into @@ Syn.LOOP @@ VarKit.toDim u, x) cx)
               val goalLoopL = makeEq tr H ((b, substVar (Syn.into Syn.DIM0, u) l), substVar (Syn.into Syn.BASE, x) cx)
               val goalLoopR = makeEq tr H ((b, substVar (Syn.into Syn.DIM1, u) l), substVar (Syn.into Syn.BASE, x) cx)               
             in
               (T.empty >: goalMotive >: goalS1 >: goalBase >: goalLoop >: goalLoopL >: goalLoopR, substVar (m, x) cx)
             end

           | O.WIF $ [[x] \ cx, _ \ m, _ \ t, _ \ f] =>
             let
               val goalMotive = makeType tr (H @> (x, AJ.TRUE @@ Syn.into Syn.WBOOL)) (cx, RedPrlKind.STABLE)             
               val goalWool = makeMem tr H (m, Syn.into Syn.WBOOL)
               val goalT = makeMem tr H (t, substVar (Syn.into Syn.TT, x) cx)
               val goalF = makeMem tr H (f, substVar (Syn.into Syn.FF, x) cx)
             in
               (T.empty >: goalMotive >: goalWool >: goalT >: goalF, substVar (m, x) cx)
             end

           | O.PROJ lbl $ [_ \ m] =>
             let
               val (psi, rcdty) = synthTerm H m
               val Abt.$ (O.RECORD lbls, args) = out @@ eval sign rcdty

               val i = #1 (Option.valOf (ListUtil.findEqIndex lbl lbls))
               val (us \ ty) = List.nth (args, i)

               (* supply the dependencies *)
               val lblPrefix = List.take (lbls, i)
               val rho = ListPair.mapEq (fn (lbl, u) => (Syn.into @@ Syn.PROJ (lbl, m), u)) (lblPrefix, us)
               val ty = VarKit.substMany rho ty
             in
               (psi, ty)
             end

           | O.PUSHOUT_REC $ [[x] \ cx, _ \ m, [xl] \ l, [xr] \ r, [ug, xg] \ g] =>
             let
               val (psi, pushoutTy) = synthTerm H m
               val Syn.PUSHOUT (lty, rty, gty, (xf, f), (xg, g)) = Syn.out pushoutTy
               val goalMotive = makeType tr (H @> (x, AJ.TRUE @@ pushoutTy)) (cx, RedPrlKind.STABLE)

               val goalLeft = makeMem tr (H @> (xl, AJ.TRUE lty)) (l, substVar (Syn.into @@ Syn.LEFT @@ VarKit.toExp xl, x) cx)
               val goalRight = makeMem tr (H @> (xr, AJ.TRUE rty)) (r, substVar (Syn.into @@ Syn.RIGHT @@ VarKit.toExp xr, x) cx)
               val goalGlue = 
                 makeMem tr
                   (H @> (ug, AJ.TERM O.DIM) @> (xg, AJ.TRUE gty))
                   (g, substVar (Syn.into @@ Syn.GLUE (VarKit.toDim ug, VarKit.toExp xg, renameVars (Var.Ctx.singleton xf xg) f, g), x) cx)
             in
               ?todo
             end

        and synthTerm H = 
            synthNeutral H o out o
              Machine.eval sign Machine.STABLE Machine.Unfolding.never
      in
        ?todo
        (* val H >> AJ.SYNTH tm = jdg
        val tm' = Machine.eval sign Machine.STABLE Machine.Unfolding.never tm
      in
        case out tm' of 
           O.CUST _ $ _ =>
           let
             val Abt.$ (O.CUST (name, _), args) = Abt.out tm
             val AJ.TRUE specTy = Sig.theoremSpec sign name args           
           in
           end
            *)
      end

    fun VarFromTrue _ jdg =
      let
        val tr = ["Synth.VarFromTrue"]
        val H >> AJ.SYNTH tm = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val AJ.TRUE a = Hyps.lookup H z
      in
        T.empty #> (H, a)
      end

    val Var = VarFromTrue
  end

  structure Misc =
  struct
    fun MatchOperator _ jdg =
      let
        val tr = ["Misc.MatchOperator"]
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

  fun Cut ajdg alpha jdg =
    let
      val tr = ["Cut"]
      val H >> ajdg' = jdg
      val z = alpha 0
      val (goal1, hole1) = makeGoal tr @@ H >> ajdg
      val (goal2, hole2) = makeGoal tr @@ (H @> (z, ajdg)) >> ajdg'
    in
      |>: goal1 >: goal2 #> (H, substVar (hole1, z) hole2)
    end

  fun CutLemma sign cust alpha jdg =
    let
      val tr = ["CutLemma"]

      val z = alpha 0
      val H >> ajdg = jdg

      val Abt.$ (O.CUST (opid, SOME ar), args) = Abt.out cust
      val zjdg = Sig.theoremSpec sign opid args

      val H' = H @> (z, zjdg)
      val (mainGoal, mainHole) = makeGoal tr @@ H' >> ajdg
      val extr = substVar (cust, z) mainHole
    in
      |>: mainGoal #> (H, extr)
    end

  fun Exact tm =
    Lcf.rule o True.Witness tm
      orelse_ Lcf.rule o Term.Exact tm


  fun lookupRule sign =
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
     | "s1/beta/loop" => Lcf.rule o S1.BetaLoop
     | "fun/eqtype" => Lcf.rule o Fun.EqType
     | "fun/eq/lam" => Lcf.rule o Fun.Eq
     | "fun/intro" => Lcf.rule o Fun.True
     | "fun/eq/eta" => Lcf.rule o Fun.Eta
     | "fun/eq/app" => Lcf.rule o Fun.EqApp
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
     | "pushout/beta/glue" => Lcf.rule o Pushout.BetaGlue
     | "coeq/eqtype" => Lcf.rule o Coequalizer.EqType
     | "coeq/eq/cod" => Lcf.rule o Coequalizer.EqCod
     | "coeq/eq/dom" => Lcf.rule o Coequalizer.EqDom
     | "coeq/eq/fcom" => Lcf.rule o Coequalizer.EqFCom
     | "coeq/beta/dom" => Lcf.rule o Coequalizer.BetaDom
     | "coeq/eq/coeq-rec" => Lcf.rule o Coequalizer.EqElim
     | "eq/eqtype" => Lcf.rule o InternalizedEquality.EqType
     | "eq/eq/ax" => Lcf.rule o InternalizedEquality.Eq
     | "eq/eta" => Lcf.rule o InternalizedEquality.Eta
     | "fcom/eqtype" => Lcf.rule o FormalComposition.EqType
     | "fcom/eq/box" => Lcf.rule o FormalComposition.Eq
     | "fcom/intro" => Lcf.rule o FormalComposition.True
     | "V/eqtype" => Lcf.rule o V.EqType
     | "V/eq/uain" => Lcf.rule o V.Eq
     | "V/intro" => Lcf.rule o V.True
     | "universe/eqtype" => Lcf.rule o Universe.EqType
     | "hcom/eq" => Lcf.rule o HCom.Eq
     | "hcom/eq/cap" => Lcf.rule o HCom.EqCapL
     | "hcom/eq/tube" => Lcf.rule o HCom.EqTubeL
     | "coe/eq" => Lcf.rule o Coe.Eq
     | "coe/eq/cap" => Lcf.rule o Coe.EqCapL
     | "subtype/eq" => Lcf.rule o SubType.Eq
     | "custom/synth" => Lcf.rule o Custom.Synth sign
     | "universe/subtype" => Lcf.rule o Universe.SubType

     | r => raise E.error [Fpp.text "No rule registered with name", Fpp.text r]

  structure Computation =
  struct
    open Computation
    fun Reduce sign = SequentReduce sign
    fun ReduceAll sign = Lcf.rule o SequentReduceAll sign
      orelse_ Lcf.rule o MatchReduce sign
      orelse_ Lcf.rule o MatchRecordReduce sign
    fun ReducePart sign = SequentReducePart sign
  end

  local
    fun fail err _ _ = Lcf.M.throw (E.errorToExn (NONE, err))

    fun matchGoal f alpha jdg =
      f jdg alpha jdg

    fun matchGoalSel Selector.IN_CONCL f = matchGoal
        (fn _ >> ajdg => f ajdg
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "matchGoalSel", Seq.pretty seq))
      | matchGoalSel (Selector.IN_HYP z) f = matchGoal
        (fn H >> _ => f (Hyps.lookup H z)
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "matchGoalSel", Seq.pretty seq))

    fun matchHyp z = matchGoalSel (Selector.IN_HYP z)

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
      NormalizeDelegate (fn ty => tac ty z) sign (Selector.IN_HYP z)

    (* trying to normalize TRUE hypothesis and then run `tac ty` *)
    and NormalizeDelegate (tac : abt -> tactic) sign =
      let
        fun go sel = matchGoalSel sel
          (fn AJ.TRUE ty =>
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
    fun NormalizeGoalDelegate tac sign = NormalizeDelegate tac sign Selector.IN_CONCL

    fun autoSynthesizableNeu sign m =
      case Syn.out m of
         Syn.VAR _ => true
       | Syn.WIF _ => true
       | Syn.S1_REC _ => true
       | Syn.APP (f, _) => autoSynthesizableNeu sign f
       | Syn.PROJ (_, t) => autoSynthesizableNeu sign t
       | Syn.DIM_APP (l, _) => autoSynthesizableNeu sign l
       | Syn.PUSHOUT_REC _ => true
       | Syn.COEQUALIZER_REC _ => true
       | Syn.CUST => true (* XXX should check the signature *)
       | _ => false
  in
    val Symmetry : tactic = matchGoal
      (fn _ >> AJ.EQ_TYPE _ => Lcf.rule o TypeEquality.Symmetry
        | _ >> AJ.TRUE _ => Lcf.rule o InternalizedEquality.Symmetry
        | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "symmetry tactic", Seq.pretty seq))

    fun SynthFromHyp z = matchHyp z
      (fn AJ.TRUE _ =>
            Lcf.rule o InternalizedEquality.NondetSynthFromTrueEq z
        | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "SynthFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

    structure Tactical =
    struct
      val NormalizeGoalDelegate = NormalizeGoalDelegate
      val NormalizeHypDelegate = NormalizeHypDelegate
    end

    local
      fun StepNeuByElim sign (m, n) =
        fn (Machine.VAR z, _) => AutoElim sign z
         | (_, Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuByElim", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm
 n])
      fun StepNeuByUnfold sign (m, n) =
        fn (Machine.METAVAR a, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuByUnfold", TermPrinter.ppMeta a)
         | (_, Machine.METAVAR a) => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuByUnfold", TermPrinter.ppMeta a)
         | (Machine.OPERATOR theta, _) => Lcf.rule o Custom.Unfold sign [theta] [Selector.IN_CONCL]
         | (_, Machine.OPERATOR theta) => Lcf.rule o Custom.Unfold sign [theta] [Selector.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuByUnfold", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepNeuExpandUntyped sign tm =
        fn Machine.VAR z => AutoElim sign z
         | Machine.OPERATOR theta => Lcf.rule o Custom.Unfold sign [theta] [Selector.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuExpandUntyped", TermPrinter.ppTerm tm)

      structure Wrapper =
      struct
        datatype mode = EQ | SUB
        fun applyEitherTac eqTac subTac =
          fn EQ => eqTac
           | SUB => subTac
        fun applyEqTac tac =
          applyEitherTac tac (Lcf.rule o SubType.Eq then_ tac)
        fun applyEitherRule eqRule subRule =
          applyEitherTac (Lcf.rule o eqRule) (Lcf.rule o subRule)
        fun applyEqRule rule = applyEqTac (Lcf.rule o rule)
      end

      fun StepEqSubTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Wrapper.applyEqRule Bool.EqType
         | (Syn.WBOOL, Syn.WBOOL) => Wrapper.applyEqRule WBool.EqType
         | (Syn.NAT, Syn.NAT) => Wrapper.applyEqRule Nat.EqType
         | (Syn.INT, Syn.INT) => Wrapper.applyEqRule Int.EqType
         | (Syn.VOID, Syn.VOID) => Wrapper.applyEqRule Void.EqType
         | (Syn.S1, Syn.S1) => Wrapper.applyEqRule S1.EqType
         | (Syn.FUN _, Syn.FUN _) => Wrapper.applyEqRule Fun.EqType
         | (Syn.RECORD _, Syn.RECORD _) => Wrapper.applyEqRule Record.EqType
         | (Syn.PATH _, Syn.PATH _) => Wrapper.applyEqRule Path.EqType
         | (Syn.LINE _, Syn.LINE _) => Wrapper.applyEqRule Line.EqType
         | (Syn.PUSHOUT _, Syn.PUSHOUT _) => Wrapper.applyEqRule Pushout.EqType
         | (Syn.COEQUALIZER _, Syn.COEQUALIZER _) => Wrapper.applyEqRule Coequalizer.EqType
         | (Syn.EQUALITY _, Syn.EQUALITY _) => Wrapper.applyEqRule InternalizedEquality.EqType
         | (Syn.FCOM _, Syn.FCOM _) => Wrapper.applyEqRule FormalComposition.EqType
         | (Syn.V _, Syn.V _) => Wrapper.applyEqRule V.EqType
         | (Syn.UNIVERSE _, Syn.UNIVERSE _) => Wrapper.applyEitherRule Universe.EqType Universe.SubType
         | _ => fn _ => fail @@ E.GENERIC [Fpp.text "Could not find type equality or subtyping rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

      fun StepEqSubTypeNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Wrapper.applyEqRule Universe.VarFromTrue
         | (Syn.WIF _, Syn.WIF _) => Wrapper.applyEqRule WBool.EqElim
         | (Syn.S1_REC _, Syn.S1_REC _) => Wrapper.applyEqRule S1.EqElim
         | (Syn.APP _, Syn.APP _) => Wrapper.applyEqRule Fun.EqApp
         | (Syn.PROJ _, Syn.PROJ _) => Wrapper.applyEqRule Record.EqProj
         | (Syn.DIM_APP (_, _), Syn.DIM_APP (_, _)) => Wrapper.applyEqRule Path.EqApp
         | (Syn.PUSHOUT_REC _, Syn.PUSHOUT_REC _) => Wrapper.applyEqRule Pushout.EqElim
         | (Syn.COEQUALIZER_REC _, Syn.COEQUALIZER_REC _) => Wrapper.applyEqRule Coequalizer.EqElim
         | (Syn.CUST, Syn.CUST) => Wrapper.applyEqRule (Custom.Eq sign)
         | _ => fn _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqTypeNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqSubTypeNeu sign tys blockers subMode =
        StepNeuByElim sign tys blockers
          orelse_
        StepEqSubTypeNeuByStruct sign tys subMode
          orelse_
        StepNeuByUnfold sign tys blockers

      fun StepEqSubType sign (ty1, ty2) subMode =
        (fn kont =>
          case (canonicity sign ty1, canonicity sign ty2) of
             (Machine.REDEX, _) => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_LEFT])
           | (_, Machine.REDEX) => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_RIGHT])
           | (Machine.CANONICAL, Machine.CANONICAL) => StepEqSubTypeVal (ty1, ty2) subMode
           | _ => kont)
        @@
        (fn kont =>
          case (Syn.out ty1, Syn.out ty2) of
             (Syn.DIM_APP (_, r), _) =>
             (case Abt.out r of
                `_ => kont
                (* XXX How about subtying? *)
               | _ => Wrapper.applyEqTac (Lcf.rule o Path.EqAppConst par Lcf.rule o Line.EqApp) subMode)
           | (_, Syn.DIM_APP (_, r)) =>
             (case Abt.out r of
                `_ => kont
                (* XXX How about subtying? *)
               | _ => Wrapper.applyEqTac (Symmetry then_ (Lcf.rule o Path.EqAppConst par Lcf.rule o Line.EqApp)) subMode)
           | _ => kont)
        @@
        (case (canonicity sign ty1, canonicity sign ty2) of
           (Machine.NEUTRAL blocker1, Machine.NEUTRAL blocker2) => StepEqSubTypeNeu sign (ty1, ty2) (blocker1, blocker2) subMode
         | (Machine.NEUTRAL blocker, Machine.CANONICAL) => StepNeuExpandUntyped sign ty1 blocker
         | (Machine.CANONICAL, Machine.NEUTRAL blocker) => Symmetry then_ StepNeuExpandUntyped sign ty2 blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqSubType",
           case subMode of
              Wrapper.EQ => AJ.pretty @@ AJ.EQ_TYPE ((ty1, ty2), K.top)
            | Wrapper.SUB => AJ.pretty @@ AJ.SUB_TYPE (ty1, ty2)))

      fun StepEqValAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_TYPE])
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Lcf.rule o Custom.Unfold sign [theta] [Selector.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqValAtType", TermPrinter.ppTerm ty)

      (* equality of canonical forms *)
      fun StepEqVal sign (m, n) ty =
        StepEqValAtType sign ty
          orelse_
        (case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.BOOL, Syn.BOOL, Syn.UNIVERSE _) => Lcf.rule o Bool.EqType
         | (Syn.TT, Syn.TT, Syn.BOOL) => Lcf.rule o Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Lcf.rule o Bool.EqFF
         | (Syn.WBOOL, Syn.WBOOL, Syn.UNIVERSE _) => Lcf.rule o WBool.EqType
         | (Syn.TT, Syn.TT, Syn.WBOOL) => Lcf.rule o WBool.EqTT
         | (Syn.FF, Syn.FF, Syn.WBOOL) => Lcf.rule o WBool.EqFF
         | (Syn.FCOM _, Syn.FCOM _, Syn.WBOOL) => Lcf.rule o WBool.EqFCom
         | (Syn.NAT, Syn.NAT, Syn.UNIVERSE _) => Lcf.rule o Nat.EqType
         | (Syn.ZERO, Syn.ZERO, Syn.NAT) => Lcf.rule o Nat.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.NAT) => Lcf.rule o Nat.EqSucc
         | (Syn.INT, Syn.INT, Syn.UNIVERSE _) => Lcf.rule o Int.EqType
         | (Syn.ZERO, Syn.ZERO, Syn.INT) => Lcf.rule o Int.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.INT) => Lcf.rule o Int.EqSucc
         | (Syn.NEGSUCC _, Syn.NEGSUCC _, Syn.INT) => Lcf.rule o Int.EqNegSucc
         | (Syn.VOID, Syn.VOID, Syn.UNIVERSE _) => Lcf.rule o Void.EqType
         | (Syn.S1, Syn.S1, Syn.UNIVERSE _) => Lcf.rule o S1.EqType
         | (Syn.BASE, Syn.BASE, Syn.S1) => Lcf.rule o S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => Lcf.rule o S1.EqLoop
         | (Syn.FCOM _, Syn.FCOM _, Syn.S1) => Lcf.rule o S1.EqFCom
         | (Syn.FUN _, Syn.FUN _, Syn.UNIVERSE _) => Lcf.rule o Fun.EqType
         | (Syn.LAM _, Syn.LAM _, Syn.FUN _) => Lcf.rule o Fun.Eq
         | (Syn.RECORD _, Syn.RECORD _, Syn.UNIVERSE _) => Lcf.rule o Record.EqType
         | (Syn.TUPLE _, Syn.TUPLE _, Syn.RECORD _) => Lcf.rule o Record.Eq
         | (Syn.PATH _, Syn.PATH _, Syn.UNIVERSE _) => Lcf.rule o Path.EqType
         | (Syn.ABS _, Syn.ABS _, Syn.PATH _) => Lcf.rule o Path.Eq
         | (Syn.LINE _, Syn.LINE _, Syn.UNIVERSE _) => Lcf.rule o Line.EqType
         | (Syn.ABS _, Syn.ABS _, Syn.LINE _) => Lcf.rule o Line.Eq
         | (Syn.PUSHOUT _, Syn.PUSHOUT _, Syn.UNIVERSE _) => Lcf.rule o Pushout.EqType
         | (Syn.LEFT _, Syn.LEFT _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqLeft
         | (Syn.RIGHT _, Syn.RIGHT _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqRight
         | (Syn.GLUE _, Syn.GLUE _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqGlue
         | (Syn.FCOM _, Syn.FCOM _, Syn.PUSHOUT _) => Lcf.rule o Pushout.EqFCom
         | (Syn.COEQUALIZER _, Syn.COEQUALIZER _, Syn.UNIVERSE _) => Lcf.rule o Coequalizer.EqType
         | (Syn.CECOD _, Syn.CECOD _, Syn.COEQUALIZER _) => Lcf.rule o Coequalizer.EqCod
         | (Syn.CEDOM _, Syn.CEDOM _, Syn.COEQUALIZER _) => Lcf.rule o Coequalizer.EqDom
         | (Syn.FCOM _, Syn.FCOM _, Syn.COEQUALIZER _) => Lcf.rule o Coequalizer.EqFCom
         | (Syn.EQUALITY _, Syn.EQUALITY _, Syn.UNIVERSE _) => Lcf.rule o InternalizedEquality.EqType
         | (Syn.AX, Syn.AX, Syn.EQUALITY _) => Lcf.rule o InternalizedEquality.Eq
         | (Syn.FCOM _, Syn.FCOM _, Syn.UNIVERSE _) => Lcf.rule o FormalComposition.EqType
         | (Syn.BOX _, Syn.BOX _, Syn.FCOM _) => Lcf.rule o FormalComposition.Eq
         | (Syn.V _, Syn.V _, Syn.UNIVERSE _) => Lcf.rule o V.EqType
         | (Syn.VIN _, Syn.VIN _, Syn.V _) => Lcf.rule o V.Eq
         | (Syn.UNIVERSE _, Syn.UNIVERSE _, Syn.UNIVERSE _) => Lcf.rule o Universe.EqType
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqVal", AJ.pretty (AJ.EQ ((m, n), ty))))

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeuAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_TYPE])
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuAtType", TermPrinter.ppTerm ty)

      fun StepEqNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Lcf.rule o InternalizedEquality.VarFromTrue
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
         | (Syn.COEQUALIZER_REC _, Syn.COEQUALIZER_REC _) => Lcf.rule o Coequalizer.EqElim
         | (Syn.CUST, Syn.CUST) => Lcf.rule o Custom.Eq sign (* XXX should consult autoSynthesizableNeu *)
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepEqNeu sign tms blockers ty =
        StepEqNeuAtType sign ty
          orelse_
        StepNeuByElim sign tms blockers
          orelse_
        StepEqNeuByStruct sign tms
          orelse_
        StepNeuByUnfold sign tms blockers

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
         | (Machine.OPERATOR theta, _) => Lcf.rule o Custom.Unfold sign [theta] [Selector.IN_CONCL])


      structure HCom =
      struct
        open HCom

        val EqCapR = Symmetry then_ Lcf.rule o EqCapL
        val EqTubeR = Symmetry then_ Lcf.rule o EqTubeL
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

        val EqCapR = Symmetry then_ Lcf.rule o EqCapL
        val AutoEqL = Lcf.rule o EqCapL orelse_ Lcf.rule o Eq
        val AutoEqR = EqCapR orelse_ Lcf.rule o Eq
        val AutoEqLR = Lcf.rule o EqCapL orelse_ EqCapR orelse_ Lcf.rule o Eq
      end

      fun ProgressCompute sign =
        Lcf.progress o (Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_TYPE, Accessor.PART_LEFT, Accessor.PART_RIGHT]))

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

      fun StepEq sign ((m, n), ty) =
        StepEqKanStruct sign (m, n)
          orelse_
        ((fn kont =>
          case (canonicity sign m, canonicity sign n) of
             (Machine.REDEX, _) => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_LEFT])
           | (_, Machine.REDEX) => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_RIGHT])
           | (Machine.CANONICAL, Machine.CANONICAL) => StepEqVal sign (m, n) ty
           | _ => kont)
        @@
        (fn kont =>
          case (Syn.out m, Syn.out n) of
             (Syn.DIM_APP (_, r), _) =>
             (case Abt.out r of
                `_ => kont
               | _ => Lcf.rule o Path.EqAppConst par Lcf.rule o Line.EqApp)
           | (_, Syn.DIM_APP (_, r)) =>
             (case Abt.out r of
                `_ => kont
               | _ => Symmetry then_ (Lcf.rule o Path.EqAppConst par Lcf.rule o Line.EqApp))
           | _ => kont)
        @@
        (case (canonicity sign m, canonicity sign n) of
            (Machine.NEUTRAL blocker1, Machine.NEUTRAL blocker2) => StepEqNeu sign (m, n) (blocker1, blocker2) ty
          | (Machine.NEUTRAL blocker, Machine.CANONICAL) => StepEqNeuExpand sign m blocker ty
          | (Machine.CANONICAL, Machine.NEUTRAL blocker) => Symmetry then_ StepEqNeuExpand sign n blocker ty
          | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", AJ.pretty @@ AJ.EQ ((m, n), ty))))

      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.RECORD [] => Lcf.rule o Record.True (* the unit type *)
         | Syn.EQUALITY (ty, m, n) => StepEq sign ((m, n), ty)
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
         | Syn.COEQUALIZER_REC _ => Lcf.rule o Coequalizer.SynthElim
         | Syn.CUST => Lcf.rule o Custom.Synth sign
         | _ => fail @@ E.GENERIC [Fpp.text "Could not find suitable type synthesis rule for", TermPrinter.ppTerm m]

      fun StepSubKind sign u =
        case (Syn.out u, canonicity sign u) of
           (_, Machine.REDEX) => Lcf.rule o Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_LEFT])
         | (_, Machine.CANONICAL) => Lcf.rule o Universe.SubKind
         | (Syn.DIM_APP (_, r), _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "SubKind with dimension application"
         | (_, Machine.NEUTRAL blocker) => StepNeuExpandUntyped sign u blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepSubKind", TermPrinter.ppTerm u)

      fun StepMatch sign u =
        case canonicity sign u of
           Machine.REDEX => Lcf.rule o Computation.MatchReduce sign
         | Machine.CANONICAL => Lcf.rule o Misc.MatchOperator
         | Machine.NEUTRAL (Machine.VAR _) => fail @@ E.NOT_APPLICABLE (Fpp.text "match", TermPrinter.ppTerm u)
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Lcf.rule o Custom.UnfoldAll sign [theta]

      fun StepMatchRecord sign u =
        case canonicity sign u of
           Machine.REDEX => Lcf.rule o Computation.MatchRecordReduce sign
         | Machine.CANONICAL => Lcf.rule o Record.MatchRecord
         | Machine.NEUTRAL (Machine.VAR _) => fail @@ E.NOT_APPLICABLE (Fpp.text "match-record", TermPrinter.ppTerm u)
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Lcf.rule o Custom.UnfoldAll sign [theta]

      fun StepJdg sign = matchGoal
        (fn _ >> AJ.EQ_TYPE (tys, _) => StepEqSubType sign tys Wrapper.EQ
          | _ >> AJ.TRUE ty => StepTrue sign ty
          | _ >> AJ.SYNTH m => StepSynth sign m
          | _ >> AJ.SUB_TYPE tys => StepEqSubType sign tys Wrapper.SUB
          | _ >> AJ.SUB_KIND (univ, _) => StepSubKind sign univ
          | MATCH (_, _, m, _) => StepMatch sign m
          | MATCH_RECORD (_, m, _) => StepMatchRecord sign m
          | _ >> jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "AutoStep", AJ.pretty jdg))

      (* favonia:
       * I temporarily disabled the checking before running the rules
       * because everything is subject to change now.
       *)

      fun NondetFromHypDelegate tac = matchGoal
        (fn H >> _ =>
              Hyps.foldr
                (fn (z, jdg, accum) => tac (z, jdg) orelse_ accum)
                (fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Fpp.text "empty context"))
                H
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))

      val NondetEqTypeFromHyp = NondetFromHypDelegate
        (fn (z, AJ.EQ_TYPE _) => Lcf.rule o TypeEquality.NondetFromEqType z
          | (z, AJ.TRUE _) =>
              Lcf.rule o TypeEquality.NondetFromTrue z
                orelse_
              Lcf.rule o InternalizedEquality.NondetTypeFromTrueEqAtType z
                orelse_
              Lcf.rule o Universe.NondetEqTypeFromTrueEqType z
          | (z, _)  => fail @@ E.NOT_APPLICABLE (Fpp.text "EqTypeFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

      val NondetTrueFromHyp = NondetFromHypDelegate
        (fn (z, AJ.TRUE _) => Lcf.rule o InternalizedEquality.NondetEqFromTrueEq z
          | (z, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "TrueFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

      val NondetSynthFromHyp = NondetFromHypDelegate (fn (z, _) => SynthFromHyp z)
    in
      val NondetStepJdgFromHyp = matchGoal
        (fn _ >> AJ.TRUE _ => NondetTrueFromHyp
          | _ >> AJ.EQ_TYPE _ => NondetEqTypeFromHyp
          | _ >> AJ.SYNTH _ => NondetSynthFromHyp
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))

      fun AutoStep sign =
        StepJdg sign

    end

    local
      fun ElimBasis sign ty z : tactic =
        case Syn.out ty of
           Syn.BOOL => Lcf.rule o Bool.Elim z
         | Syn.WBOOL => Lcf.rule o WBool.Elim z
         | Syn.NAT => Lcf.rule o Nat.Elim z
         | Syn.INT => Lcf.rule o Int.Elim z
         | Syn.VOID => Lcf.rule o Void.Elim z
         | Syn.S1 => Lcf.rule o S1.Elim z
         | Syn.FUN _ => Lcf.rule o MultiArrow.Elim sign 1 z
         | Syn.RECORD _ => Lcf.rule o Record.Elim z
         | Syn.PATH _ => Lcf.rule o MultiArrow.Elim sign 1 z
         | Syn.LINE _ => Lcf.rule o MultiArrow.Elim sign 1 z
         | Syn.PUSHOUT _ => Lcf.rule o Pushout.Elim z
         | Syn.COEQUALIZER _ => Lcf.rule o Coequalizer.Elim z
         | Syn.EQUALITY _ => Lcf.rule o InternalizedEquality.Elim z
         | _ => fail @@ E.GENERIC [Fpp.text "elim tactic", TermPrinter.ppTerm ty]
    in
      fun Elim sign = NormalizeHypDelegate (ElimBasis sign) sign
    end

    fun Rewrite _ sel m = Lcf.rule o InternalizedEquality.Rewrite sel m

    fun Inversion z : tactic = Lcf.rule o Record.EqInv z
  end
end
