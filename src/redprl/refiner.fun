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
  type rule = Lcf.jdg Lcf.rule
  type hyp = Sym.t
  type ajdg = AJ.jdg
  type opid = Sig.opid
  type rule_name = string

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix orelse_ then_ thenl

  structure Hyp =
  struct
    fun Project z jdg =
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

    fun Delete z jdg =
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

  structure Names = 
  struct

    fun Push xs = 
      fn jdg as _ >> _ => 
         let
           val jdg' as H >> _ = Sequent.push xs jdg handle _ => jdg
           val (goal, hole) = makeGoal [] jdg'
         in
           Lcf.|> (|>: goal, abstractEvidence H hole)
         end
      
    fun PopAs xs jdg = 
      let
        val jdg' as H >> _ = Sequent.popAs xs jdg handle _ => jdg
        val (goal, hole) = makeGoal [] jdg'
      in
        Lcf.|> (|>: goal, abstractEvidence H hole)
      end
    
  end

  structure TypeEquality =
  struct
    fun Symmetry jdg =
      let
        val tr = ["TypeEquality.Symmetry"]
        val H >> AJ.EQ_TYPE ((ty1, ty2), k) = jdg
        val goal = makeEqType tr H ((ty2, ty1), k)
      in
        |>: goal #> (H, axiom)
      end

    (* this is for non-deterministic search *)
    fun NondetFromEqType z jdg =
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
    fun NondetFromTrue z jdg =
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
    fun Eq jdg =
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
    fun Witness tm jdg =
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
    fun Exact tm jdg =
      let
        val tr = ["Term.Exact"]
        val H >> AJ.TERM tau = jdg
        val tau' = Abt.sort tm
        val _ = Assert.sortEq (tau, tau')
      in
        T.empty #> (H, tm)
      end
  end

  fun Cut ajdg jdg =
    let
      val tr = ["Cut"]
      val H >> ajdg' = jdg
      val z = Sym.new ()
      val (goal1, hole1) = makeGoal tr @@ H >> ajdg
      val (goal2, hole2) = makeGoal tr @@ (H @> (z, ajdg)) >> ajdg'
    in
      |>: goal1 >: goal2 #> (H, substVar (hole1, z) hole2)
    end

  fun CutLemma sign cust jdg =
    let
      val tr = ["CutLemma"]

      val z = Sym.new ()
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
    Lcf.rule (True.Witness tm)
      orelse_ Lcf.rule (Term.Exact tm)


  fun lookupRule sign =
    fn "bool/eqtype" => Lcf.rule Bool.EqType
     | "bool/eq/tt" => Lcf.rule Bool.EqTT
     | "bool/eq/ff" => Lcf.rule Bool.EqFF
     | "bool/eq/if" => Lcf.rule @@ Bool.EqElim sign
     | "nat/eqtype" => Lcf.rule Nat.EqType
     | "nat/eq/zero" => Lcf.rule Nat.EqZero
     | "nat/eq/succ" => Lcf.rule Nat.EqSucc
     | "nat/eq/nat-rec" => Lcf.rule Nat.EqElim
     | "int/eqtype" => Lcf.rule Int.EqType
     | "int/eq/zero" => Lcf.rule Int.EqZero
     | "int/eq/succ" => Lcf.rule Int.EqSucc
     | "int/eq/negsucc" => Lcf.rule Int.EqNegSucc
     | "int/eq/int-rec" => Lcf.rule Int.EqElim
     | "void/eqtype" => Lcf.rule Void.EqType
     | "s1/eqtype" => Lcf.rule S1.EqType
     | "s1/eq/base" => Lcf.rule S1.EqBase
     | "s1/eq/loop" => Lcf.rule S1.EqLoop
     | "s1/eq/fcom" => Lcf.rule S1.EqFCom
     | "s1/eq/s1-rec" => Lcf.rule S1.EqElim
     | "s1/beta/loop" => Lcf.rule S1.BetaLoop
     | "fun/eqtype" => Lcf.rule Fun.EqType
     | "fun/eq/lam" => Lcf.rule Fun.Eq
     | "fun/intro" => Lcf.rule Fun.True
     | "fun/eq/eta" => Lcf.rule Fun.Eta
     | "fun/eq/app" => Lcf.rule @@ Fun.EqApp sign
     | "record/eqtype" => Lcf.rule Record.EqType
     | "record/eq/tuple" => Lcf.rule Record.Eq
     | "record/eq/eta" => Lcf.rule Record.Eta
     | "record/eq/proj" => Lcf.rule @@ Record.EqProj sign
     | "record/intro" => Lcf.rule Record.True
     | "path/eqtype" => Lcf.rule Path.EqType
     | "path/eq/abs" => Lcf.rule Path.Eq
     | "path/intro" => Lcf.rule Path.True
     | "path/eq/eta" => Lcf.rule Path.Eta
     | "path/eq/app" => Lcf.rule @@ Path.EqApp sign
     | "path/eq/app/const" => Lcf.rule @@ Path.EqAppConst sign
     | "path/eq/from-line" => Lcf.rule Path.EqFromLine
     | "line/eqtype" => Lcf.rule Line.EqType
     | "line/eq/abs" => Lcf.rule Line.Eq
     | "line/intro" => Lcf.rule Line.True
     | "line/eq/eta" => Lcf.rule Line.Eta
     | "line/eq/app" => Lcf.rule @@ Line.EqApp sign
     | "pushout/eqtype" => Lcf.rule Pushout.EqType
     | "pushout/eq/left" => Lcf.rule Pushout.EqLeft
     | "pushout/eq/right" => Lcf.rule Pushout.EqRight
     | "pushout/eq/glue" => Lcf.rule Pushout.EqGlue
     | "pushout/eq/fcom" => Lcf.rule Pushout.EqFCom
     | "pushout/eq/pushout-rec" => Lcf.rule @@ Pushout.EqElim sign
     | "pushout/beta/glue" => Lcf.rule Pushout.BetaGlue
     | "coeq/eqtype" => Lcf.rule Coequalizer.EqType
     | "coeq/eq/cod" => Lcf.rule Coequalizer.EqCod
     | "coeq/eq/dom" => Lcf.rule Coequalizer.EqDom
     | "coeq/eq/fcom" => Lcf.rule Coequalizer.EqFCom
     | "coeq/beta/dom" => Lcf.rule Coequalizer.BetaDom
     | "coeq/eq/coeq-rec" => Lcf.rule @@ Coequalizer.EqElim sign
     | "eq/eqtype" => Lcf.rule InternalizedEquality.EqType
     | "eq/eq/ax" => Lcf.rule InternalizedEquality.Eq
     | "eq/eta" => Lcf.rule InternalizedEquality.Eta
     | "fcom/eqtype" => Lcf.rule FormalComposition.EqType
     | "fcom/eq/box" => Lcf.rule FormalComposition.Eq
     | "fcom/intro" => Lcf.rule FormalComposition.True
     | "V/eqtype" => Lcf.rule V.EqType
     | "V/eq/uain" => Lcf.rule V.Eq
     | "V/intro" => Lcf.rule V.True
     | "V/eq/proj" => Lcf.rule @@ V.EqProj sign
     | "universe/eqtype" => Lcf.rule Universe.EqType
     | "hcom/eq" => Lcf.rule HCom.Eq
     | "hcom/eq/cap" => Lcf.rule HCom.EqCapL
     | "hcom/eq/tube" => Lcf.rule HCom.EqTubeL
     | "coe/eq" => Lcf.rule Coe.Eq
     | "coe/eq/cap" => Lcf.rule Coe.EqCapL
     | "subtype/eq" => Lcf.rule SubType.Eq
     | "universe/subtype" => Lcf.rule Universe.SubType
     | r => raise E.error [Fpp.text "No rule registered with name", Fpp.text r]

  structure Computation =
  struct
    open Computation
    fun Reduce sign = SequentReduce sign
    fun ReduceAll sign = Lcf.rule @@ SequentReduceAll sign
    fun ReducePart sign = SequentReducePart sign
  end

  local
    fun fail err _ = Lcf.M.throw (E.errorToExn (NONE, err))

    fun matchGoal f jdg =
      f jdg jdg

    fun matchGoalSel Selector.IN_CONCL f = matchGoal
        (fn _ >> ajdg => f ajdg)
      | matchGoalSel (Selector.IN_HYP z) f = matchGoal
        (fn H >> _ => f (Hyps.lookup H z))

    fun matchHyp z = matchGoalSel (Selector.IN_HYP z)

    fun canonicity sign =
      Machine.canonicity sign Machine.NOMINAL (Machine.Unfolding.default sign)

    fun AutoElimBasis ty z : tactic =
      case Syn.out ty of
         Syn.BOOL => Lcf.rule @@ Bool.Elim z
       | Syn.VOID => Lcf.rule @@ Void.Elim z
       | Syn.EQUALITY _ => Lcf.rule @@ InternalizedEquality.Elim z
       | Syn.RECORD _ => Lcf.rule @@ Record.Elim z
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
                Machine.REDEX => Lcf.rule (Computation.SequentReduce sign [sel]) then_ go sel
              | Machine.NEUTRAL (Machine.VAR z') => (AutoElim sign z' then_ go sel) orelse_ tac ty
              | Machine.NEUTRAL (Machine.OPERATOR theta) => (Lcf.rule @@ Custom.Unfold sign [theta] [sel]) then_ go sel
              | _ => tac ty)
            | jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "Normalize", AJ.pretty jdg))
      in
        go
      end

    (* trying to normalize TRUE goal and then run `tac ty` *)
    fun NormalizeGoalDelegate tac sign = NormalizeDelegate tac sign Selector.IN_CONCL
  in
    val Symmetry : tactic = matchGoal
      (fn _ >> AJ.EQ_TYPE _ => Lcf.rule TypeEquality.Symmetry
        | _ >> AJ.TRUE _ => Lcf.rule InternalizedEquality.Symmetry
        | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "symmetry tactic", Seq.pretty seq))

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
         | (Machine.OPERATOR theta, _) => Lcf.rule @@ Custom.UnfoldPart sign [theta] (Selector.IN_CONCL, [Accessor.PART_LEFT])
         | (_, Machine.OPERATOR theta) => Lcf.rule @@ Custom.UnfoldPart sign [theta] (Selector.IN_CONCL, [Accessor.PART_RIGHT])
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuByUnfold", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n])

      fun StepNeuExpandUntyped sign part tm =
        fn Machine.VAR z => AutoElim sign z
         | Machine.OPERATOR theta => Lcf.rule @@ Custom.UnfoldPart sign [theta] (Selector.IN_CONCL, [part])
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepNeuExpandUntyped", TermPrinter.ppTerm tm)

      structure Wrapper =
      struct
        datatype mode = EQ | SUB
        fun applyEitherTac eqTac subTac =
          fn EQ => eqTac
           | SUB => subTac
        fun applyEqTac tac =
          applyEitherTac tac (Lcf.rule SubType.Eq then_ tac)
        fun applyEitherRule eqRule subRule =
          applyEitherTac (Lcf.rule eqRule) (Lcf.rule subRule)
        fun applyEqRule rule = applyEqTac (Lcf.rule rule)
      end

      fun StepEqSubTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Wrapper.applyEqRule Bool.EqType
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
         | (Syn.IF _, Syn.IF _) => Wrapper.applyEqRule (Bool.EqElim sign)
         | (Syn.S1_REC _, Syn.S1_REC _) => Wrapper.applyEqRule S1.EqElim
         | (Syn.NAT_REC _, Syn.NAT_REC _) => Wrapper.applyEqRule Nat.EqElim
         | (Syn.INT_REC _, Syn.INT_REC _) => Wrapper.applyEqRule Int.EqElim
         | (Syn.APP _, Syn.APP _) => Wrapper.applyEqRule (Fun.EqApp sign)
         | (Syn.PROJ _, Syn.PROJ _) => Wrapper.applyEqRule (Record.EqProj sign)
         | (Syn.DIM_APP (_, _), Syn.DIM_APP (_, _)) => (fn mode => Wrapper.applyEqRule (Path.EqApp sign) mode orelse_ Wrapper.applyEqRule (Line.EqApp sign) mode)
         | (Syn.PUSHOUT_REC _, Syn.PUSHOUT_REC _) => Wrapper.applyEqRule @@ Pushout.EqElim sign
         | (Syn.COEQUALIZER_REC _, Syn.COEQUALIZER_REC _) => Wrapper.applyEqRule @@ Coequalizer.EqElim sign
         | (Syn.VPROJ _, Syn.VPROJ _) => Wrapper.applyEqRule @@ V.EqProj sign
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
             (Machine.REDEX, _) => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_LEFT])
           | (_, Machine.REDEX) => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_RIGHT])
           | (Machine.CANONICAL, Machine.CANONICAL) => StepEqSubTypeVal (ty1, ty2) subMode
           | _ => kont)
        @@
        (fn kont =>
          case (Syn.out ty1, Syn.out ty2) of
             (Syn.DIM_APP (_, r), _) =>
             (case Abt.out r of
                `_ => kont
                (* XXX How about subtying? *)
               | _ => Wrapper.applyEqTac (Lcf.rule (Path.EqAppConst sign) orelse_ Lcf.rule (Line.EqApp sign)) subMode)
           | (_, Syn.DIM_APP (_, r)) =>
             (case Abt.out r of
                `_ => kont
                (* XXX How about subtying? *)
               | _ => Wrapper.applyEqTac (Symmetry then_ (Lcf.rule (Path.EqAppConst sign) orelse_ Lcf.rule (Line.EqApp sign))) subMode)
           | _ => kont)
        @@
        (case (canonicity sign ty1, canonicity sign ty2) of
           (Machine.NEUTRAL blocker1, Machine.NEUTRAL blocker2) => StepEqSubTypeNeu sign (ty1, ty2) (blocker1, blocker2) subMode
         | (Machine.NEUTRAL blocker, Machine.CANONICAL) => StepNeuExpandUntyped sign Accessor.PART_LEFT ty1 blocker
         | (Machine.CANONICAL, Machine.NEUTRAL blocker) => StepNeuExpandUntyped sign Accessor.PART_RIGHT ty2 blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqSubType",
           case subMode of
              Wrapper.EQ => AJ.pretty @@ AJ.EQ_TYPE ((ty1, ty2), K.top)
            | Wrapper.SUB => AJ.pretty @@ AJ.SUB_TYPE (ty1, ty2)))

      fun StepEqValAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_TYPE])
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | Machine.NEUTRAL (Machine.OPERATOR theta) => Lcf.rule @@ Custom.Unfold sign [theta] [Selector.IN_CONCL]
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqValAtType", TermPrinter.ppTerm ty)

      (* equality of canonical forms *)
      fun StepEqVal sign (m, n) ty =
        StepEqValAtType sign ty
          orelse_
        (case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.BOOL, Syn.BOOL, Syn.UNIVERSE _) => Lcf.rule Bool.EqType
         | (Syn.TT, Syn.TT, Syn.BOOL) => Lcf.rule Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Lcf.rule Bool.EqFF
         | (Syn.NAT, Syn.NAT, Syn.UNIVERSE _) => Lcf.rule Nat.EqType
         | (Syn.ZERO, Syn.ZERO, Syn.NAT) => Lcf.rule Nat.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.NAT) => Lcf.rule Nat.EqSucc
         | (Syn.INT, Syn.INT, Syn.UNIVERSE _) => Lcf.rule Int.EqType
         | (Syn.ZERO, Syn.ZERO, Syn.INT) => Lcf.rule Int.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.INT) => Lcf.rule Int.EqSucc
         | (Syn.NEGSUCC _, Syn.NEGSUCC _, Syn.INT) => Lcf.rule Int.EqNegSucc
         | (Syn.VOID, Syn.VOID, Syn.UNIVERSE _) => Lcf.rule Void.EqType
         | (Syn.S1, Syn.S1, Syn.UNIVERSE _) => Lcf.rule S1.EqType
         | (Syn.BASE, Syn.BASE, Syn.S1) => Lcf.rule S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => Lcf.rule S1.EqLoop
         | (Syn.FCOM _, Syn.FCOM _, Syn.S1) => Lcf.rule S1.EqFCom
         | (Syn.FUN _, Syn.FUN _, Syn.UNIVERSE _) => Lcf.rule Fun.EqType
         | (Syn.LAM _, Syn.LAM _, Syn.FUN _) => Lcf.rule Fun.Eq
         | (Syn.RECORD _, Syn.RECORD _, Syn.UNIVERSE _) => Lcf.rule Record.EqType
         | (Syn.TUPLE _, Syn.TUPLE _, Syn.RECORD _) => Lcf.rule Record.Eq
         | (Syn.PATH _, Syn.PATH _, Syn.UNIVERSE _) => Lcf.rule Path.EqType
         | (Syn.ABS _, Syn.ABS _, Syn.PATH _) => Lcf.rule Path.Eq
         | (Syn.LINE _, Syn.LINE _, Syn.UNIVERSE _) => Lcf.rule Line.EqType
         | (Syn.ABS _, Syn.ABS _, Syn.LINE _) => Lcf.rule Line.Eq
         | (Syn.PUSHOUT _, Syn.PUSHOUT _, Syn.UNIVERSE _) => Lcf.rule Pushout.EqType
         | (Syn.LEFT _, Syn.LEFT _, Syn.PUSHOUT _) => Lcf.rule Pushout.EqLeft
         | (Syn.RIGHT _, Syn.RIGHT _, Syn.PUSHOUT _) => Lcf.rule Pushout.EqRight
         | (Syn.GLUE _, Syn.GLUE _, Syn.PUSHOUT _) => Lcf.rule Pushout.EqGlue
         | (Syn.FCOM _, Syn.FCOM _, Syn.PUSHOUT _) => Lcf.rule Pushout.EqFCom
         | (Syn.COEQUALIZER _, Syn.COEQUALIZER _, Syn.UNIVERSE _) => Lcf.rule Coequalizer.EqType
         | (Syn.CECOD _, Syn.CECOD _, Syn.COEQUALIZER _) => Lcf.rule Coequalizer.EqCod
         | (Syn.CEDOM _, Syn.CEDOM _, Syn.COEQUALIZER _) => Lcf.rule Coequalizer.EqDom
         | (Syn.FCOM _, Syn.FCOM _, Syn.COEQUALIZER _) => Lcf.rule Coequalizer.EqFCom
         | (Syn.EQUALITY _, Syn.EQUALITY _, Syn.UNIVERSE _) => Lcf.rule InternalizedEquality.EqType
         | (Syn.AX, Syn.AX, Syn.EQUALITY _) => Lcf.rule InternalizedEquality.Eq
         | (Syn.FCOM _, Syn.FCOM _, Syn.UNIVERSE _) => Lcf.rule FormalComposition.EqType
         | (Syn.BOX _, Syn.BOX _, Syn.FCOM _) => Lcf.rule FormalComposition.Eq
         | (Syn.V _, Syn.V _, Syn.UNIVERSE _) => Lcf.rule V.EqType
         | (Syn.VIN _, Syn.VIN _, Syn.V _) => Lcf.rule V.Eq
         | (Syn.UNIVERSE _, Syn.UNIVERSE _, Syn.UNIVERSE _) => Lcf.rule Universe.EqType
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqVal", AJ.pretty (AJ.EQ ((m, n), ty))))

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeuAtType sign ty =
        case canonicity sign ty of
           Machine.REDEX => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_TYPE])
         | Machine.NEUTRAL (Machine.VAR z) => AutoElim sign z
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuAtType", TermPrinter.ppTerm ty)

      fun StepEqNeuByStruct sign (m, n) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Lcf.rule InternalizedEquality.VarFromTrue
         | (Syn.IF _, Syn.IF _) => Lcf.rule @@ Bool.EqElim sign
         | (Syn.S1_REC _, Syn.S1_REC _) => Lcf.rule S1.EqElim
         | (Syn.NAT_REC _, Syn.NAT_REC _) => Lcf.rule Nat.EqElim
         | (Syn.INT_REC _, Syn.INT_REC _) => Lcf.rule Int.EqElim
         | (Syn.PROJ _, Syn.PROJ _) => Lcf.rule @@ Record.EqProj sign
         | (Syn.APP (f, _), Syn.APP _) => Lcf.rule @@ Fun.EqApp sign
         | (Syn.DIM_APP (_, r1), Syn.DIM_APP (_, r2)) =>
           (case (Abt.out r1, Abt.out r2) of
               (`_, `_) => Lcf.rule (Path.EqApp sign) orelse_ Lcf.rule (Line.EqApp sign)
             | _ =>  fail @@ E.NOT_APPLICABLE (Fpp.text "StepEqNeuByStruct", Fpp.hvsep [TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n]))
         | (Syn.PUSHOUT_REC _, Syn.PUSHOUT_REC _) => Lcf.rule @@ Pushout.EqElim sign
         | (Syn.COEQUALIZER_REC _, Syn.COEQUALIZER_REC _) => Lcf.rule @@ Coequalizer.EqElim sign
         | (Syn.VPROJ _, Syn.VPROJ _) => Lcf.rule @@ V.EqProj sign
         | (Syn.CUST, Syn.CUST) => Lcf.rule @@ Custom.Eq sign
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
           (_, Syn.FUN _) => Lcf.rule Fun.Eta
         | (_, Syn.RECORD _) => Lcf.rule Record.Eta
         | (_, Syn.PATH _) => Lcf.rule Path.Eta
         | (_, Syn.LINE _) => Lcf.rule Line.Eta
         | (_, Syn.EQUALITY _) => Lcf.rule InternalizedEquality.Eta
         | (Machine.VAR z, _) => AutoElim sign z
         | (Machine.OPERATOR theta, _) => Lcf.rule @@ Custom.UnfoldPart sign [theta] (Selector.IN_CONCL, [Accessor.PART_LEFT]))


      structure HCom =
      struct
        open HCom

        val EqCapR = Symmetry then_ Lcf.rule EqCapL
        val EqTubeR = Symmetry then_ Lcf.rule EqTubeL
        val AutoEqL = Lcf.rule EqCapL orelse_ Lcf.rule EqTubeL orelse_  Lcf.rule Eq
        val AutoEqR = EqCapR orelse_ EqTubeR orelse_ Lcf.rule Eq

        (* Try all the hcom rules.
         * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
        val AutoEqLR =
          Lcf.rule EqCapL orelse_ EqCapR orelse_
          Lcf.rule EqTubeL orelse_ EqTubeR orelse_
          Lcf.rule Eq
      end

      structure Coe =
      struct
        open Coe

        val EqCapR = Symmetry then_ Lcf.rule EqCapL
        val AutoEqL = Lcf.rule EqCapL orelse_ Lcf.rule Eq
        val AutoEqR = EqCapR orelse_ Lcf.rule Eq
        val AutoEqLR = Lcf.rule EqCapL orelse_ EqCapR orelse_ Lcf.rule Eq
      end

      fun ProgressCompute sign =
        Lcf.progress @@ Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_TYPE, Accessor.PART_LEFT, Accessor.PART_RIGHT])

      fun ComputeBefore sign tac =
        (ProgressCompute sign then_ tac) orelse_ tac

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
             (Machine.REDEX, _) => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_LEFT])
           | (_, Machine.REDEX) => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_RIGHT])
           | (Machine.CANONICAL, Machine.CANONICAL) => StepEqVal sign (m, n) ty
           | _ => kont)
        @@
        (fn kont =>
          case (Syn.out m, Syn.out n) of
             (Syn.DIM_APP (_, r), _) =>
             (case Abt.out r of
                `_ => kont
               | _ => Lcf.rule (Path.EqAppConst sign) orelse_ Lcf.rule (Line.EqApp sign))
           | (_, Syn.DIM_APP (_, r)) =>
             (case Abt.out r of
                `_ => kont
               | _ => Symmetry then_ (Lcf.rule (Path.EqAppConst sign) orelse_ Lcf.rule (Line.EqApp sign)))
           | _ => kont)
        @@
        (case (canonicity sign m, canonicity sign n) of
            (Machine.NEUTRAL blocker1, Machine.NEUTRAL blocker2) => StepEqNeu sign (m, n) (blocker1, blocker2) ty
          | (Machine.NEUTRAL blocker, Machine.CANONICAL) => StepEqNeuExpand sign m blocker ty
          | (Machine.CANONICAL, Machine.NEUTRAL blocker) => Symmetry then_ StepEqNeuExpand sign n blocker ty
          | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepEq", AJ.pretty @@ AJ.EQ ((m, n), ty))))

      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.RECORD [] => Lcf.rule Record.True (* the unit type *)
         | Syn.EQUALITY (ty, m, n) => StepEq sign ((m, n), ty)
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepTrue", TermPrinter.ppTerm ty)

      fun StepSubKind sign u =
        case (Syn.out u, canonicity sign u) of
           (_, Machine.REDEX) => Lcf.rule @@ Computation.SequentReducePart sign (Selector.IN_CONCL, [Accessor.PART_LEFT])
         | (_, Machine.CANONICAL) => Lcf.rule Universe.SubKind
         | (Syn.DIM_APP (_, r), _) => fail @@ E.UNIMPLEMENTED @@ Fpp.text "SubKind with dimension application"
         | (_, Machine.NEUTRAL blocker) => StepNeuExpandUntyped sign Accessor.PART_LEFT u blocker
         | _ => fail @@ E.NOT_APPLICABLE (Fpp.text "StepSubKind", TermPrinter.ppTerm u)

      fun StepJdg sign = matchGoal
        (fn _ >> AJ.EQ_TYPE (tys, _) => StepEqSubType sign tys Wrapper.EQ
          | _ >> AJ.TRUE ty => StepTrue sign ty
          | _ >> AJ.SUB_TYPE tys => StepEqSubType sign tys Wrapper.SUB
          | _ >> AJ.SUB_KIND (univ, _) => StepSubKind sign univ
          | _ >> jdg => fail @@ E.NOT_APPLICABLE (Fpp.text "AutoStep", AJ.pretty jdg))

      (* favonia:
       * I temporarily disabled the checking before running the rules
       * because everything is subject to change now.
       *)

      fun NondetFromHypDelegate sign tac = matchGoal
        (fn H >> _ =>
              Hyps.foldr
                (fn (z, jdg, accum) => tac (z, jdg) orelse_ accum)
                (fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Fpp.text "empty context"))
                H)

      fun NondetEqTypeFromHyp sign = NondetFromHypDelegate sign
        (fn (z, AJ.EQ_TYPE _) => Lcf.rule @@ TypeEquality.NondetFromEqType z
          | (z, AJ.TRUE _) =>
              Lcf.rule (Void.Elim z)
                orelse_
              Lcf.rule (TypeEquality.NondetFromTrue z)
                orelse_
              Lcf.rule (InternalizedEquality.NondetTypeFromTrueEqAtType z)
                orelse_
              Lcf.rule (Universe.NondetEqTypeFromTrueEqType z)
          | (z, _)  => fail @@ E.NOT_APPLICABLE (Fpp.text "EqTypeFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

      fun NondetTrueFromHyp sign = NondetFromHypDelegate sign
        (fn (z, AJ.TRUE _) => Lcf.rule (InternalizedEquality.NondetEqFromTrueEq z) orelse_ Lcf.rule (Void.Elim z)
          | (z, _) => fail @@ E.NOT_APPLICABLE (Fpp.text "TrueFromHyp", Fpp.hsep [Fpp.text "hyp", TermPrinter.ppVar z]))

    in
      fun NondetStepJdgFromHyp sign = matchGoal
        (fn _ >> AJ.TRUE _ => NondetTrueFromHyp sign
          | _ >> AJ.EQ_TYPE _ => NondetEqTypeFromHyp sign
          | seq => fail @@ E.NOT_APPLICABLE (Fpp.text "non-deterministic search", Seq.pretty seq))

      fun AutoStep sign =
        StepJdg sign

    end

    local
      fun ElimBasis sign ty z : tactic =
        case Syn.out ty of
           Syn.BOOL => Lcf.rule @@ Bool.Elim z
         | Syn.NAT => Lcf.rule @@ Nat.Elim z
         | Syn.INT => Lcf.rule @@ Int.Elim z
         | Syn.VOID => Lcf.rule @@ Void.Elim z
         | Syn.S1 => Lcf.rule @@ S1.Elim z
         | Syn.FUN _ => Lcf.rule @@ MultiArrow.Elim sign 1 z
         | Syn.RECORD _ => Lcf.rule @@ Record.Elim z
         | Syn.PATH _ => Lcf.rule @@ MultiArrow.Elim sign 1 z
         | Syn.LINE _ => Lcf.rule @@ MultiArrow.Elim sign 1 z
         | Syn.PUSHOUT _ => Lcf.rule @@ Pushout.Elim z
         | Syn.COEQUALIZER _ => Lcf.rule @@ Coequalizer.Elim z
         | Syn.EQUALITY _ => Lcf.rule @@ InternalizedEquality.Elim z
         | _ => fail @@ E.GENERIC [Fpp.text "elim tactic", TermPrinter.ppTerm ty]
    in
      fun Elim sign = NormalizeHypDelegate (ElimBasis sign) sign
    end

    fun Rewrite sign (sel, accs) m = Lcf.rule @@ InternalizedEquality.Rewrite sign (sel, accs) m

    fun Inversion z : tactic = Lcf.rule @@ Record.EqInv z
  end
end
