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
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  structure TypeRules = RefinerTypeRules (Sig)
  open RedPrlAbt Kit ComRefinerKit TypeRules

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = abt CJ.jdg
  type opid = Sig.opid

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
        val catjdg' = lookupHyp H z
      in
        if CJ.eq (catjdg, catjdg') then
          T.empty #> (I, H, Syn.into (Syn.VAR (z, CJ.synthesis catjdg)))
        else
          raise E.error
            [Fpp.text "Hypothesis",
             Fpp.expr @@ Fpp.hsep [TermPrinter.ppSym z, Fpp.Atomic.colon, CJ.pretty' TermPrinter.ppTerm catjdg'],
             Fpp.text "does not match goal",
             CJ.pretty' TermPrinter.ppTerm catjdg]
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected sequent judgment"]
  end

  structure TypeEquality =
  struct
    fun Symmetry _ jdg =
    let
      val _ = RedPrlLog.trace "Equality.Symmetry"
      val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
      val goal = makeEqType (I, H) (ty2, ty1)
    in
      |>: goal #> (I, H, trivial)
    end
  end

  structure Truth =
  struct
    fun Witness tm _ jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> CJ.TRUE ty = jdg
        val goal = makeMem (I, H) (tm, ty)
      in
        |>: goal #> (I, H, tm)
      end
      handle Bind =>
        raise E.error [Fpp.text @@ "Expected truth sequent but got " ^ J.toString jdg]
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
    fun FromWfHyp z _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromWfHyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val CJ.EQ ((a, b), ty) = lookupHyp H z
      in
        if Abt.eq (a, tm) orelse Abt.eq (b, tm) then
          T.empty #> (I, H, ty)
        else
          raise Fail "Did not match"
      end

    fun Hyp _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Hyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val CJ.TRUE a = lookupHyp H z
      in
        T.empty #> (I, H, a)
      end

    fun WIf _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.If"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.WIF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem (I, H) (tm, cm)
      in
        |>: goal #> (I, H, cm)
      end

    fun S1Rec _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.S1Rec"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.S1_REC ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem (I, H) (tm, cm)
      in
        |>: goal #> (I, H, cm)
      end

    fun App _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.App"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.APP (m, n) = Syn.out tm
        val (goalDFun, holeDFun) = makeSynth (I, H) m
        val (goalDom, holeDom) = makeMatch (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeMatch (O.MONO O.DFUN, 1, holeDFun, [], [n])
        val goalN = makeMem (I, H) (n, holeDom)
      in
        |>: goalDFun >: goalDom >: goalCod >: goalN #> (I, H, holeCod)
      end

    fun PathApp _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.PathApp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.PATH_APP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeSynth (I, H) m
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holePathTy, [r], [])
      in
        |>: goalPathTy >: goalLine #> (I, H, holeLine)
      end

    fun Fst _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Fst"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.FST m = Syn.out tm
        val (goalTy, holeTy) = makeSynth (I, H) m
        val (goalA, holeA) = makeMatch (O.MONO O.DPROD, 0, holeTy, [], [])
      in
        |>: goalTy >: goalA #> (I, H, holeA)
      end

    fun Snd _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Snd"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.SND m = Syn.out tm
        val (goalTy, holeTy) = makeSynth (I, H) m
        val (goalB, holeB) = makeMatch (O.MONO O.DPROD, 1, holeTy, [], [Syn.into @@ Syn.FST m])
      in
        |>: goalTy >: goalB #> (I, H, holeB)
      end
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

        val arg' = substSymenv srho (substVarenv vrho arg)
      in
        Lcf.|> (T.empty, abtToAbs arg')
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH judgment failed to unify"]

    fun DimSubst _ jdg = 
      let
        val _ = RedPrlLog.trace "Misc.DimSubst"
        val DIM_SUBST (rtm, u, m) = jdg
        val Abt.$ (O.POLY (O.DIM_REF r), _) = Abt.out rtm
      in
        Lcf.|> (T.empty, abtToAbs (substSymbol (r, u) m))
      end
  end

  structure Equality =
  struct
    fun Hyp _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Hyp"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val catjdg = lookupHyp H x
        val ty' =
          case catjdg of
             CJ.TRUE ty => ty
           | _ => raise E.error [Fpp.text "Equality.Hyp: expected truth hypothesis"]

        (* If the types are identical, there is no need to create a new subgoal (which would amount to proving that 'ty' is a type).
           This is because the semantics of sequents is that by assuming that something is a member of a 'ty', we have
           automatically assumed that 'ty' is a type. *)
        val goalTy = makeEqTypeIfDifferent (I, H) (ty, ty')
      in
        |>:? goalTy #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected variable-equality sequent"]

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val goal = makeEq (I, H) ((n, m), ty)
      in
        |>: goal #> (I, H, trivial)
      end
  end

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COE {dir=(r0, r'0), ty=(u0, ty0), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=(r1, r'1), ty=(u1, ty1), coercee=m1} = Syn.out rhs
        val () = Assert.paramEq "Coe.Eq source of direction" (r0, r1)
        val () = Assert.paramEq "Coe.Eq target of direction" (r'0, r'1)

        (* type *)
        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u0) ty0
        val ty1w = substSymbol (P.ret w, u1) ty1
        val goalTy = makeEqType (I @ [(w, P.DIM)], H) (ty0w, ty1w)
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r' = substSymbol (r'0, u0) ty0
        val goalTy0 = makeEqTypeIfDifferent (I, H) (ty0r', ty)

        (* coercee *)
        val ty0r = substSymbol (r0, u0) ty0
        val goalCoercees = makeEq (I, H) ((m0, m1), ty0r)
      in
        |>: goalCoercees >:? goalTy0 >: goalTy #> (I, H, trivial)
      end

    fun CapEqL _ jdg =
      let
        val _ = RedPrlLog.trace "Coe.CapEq"
        val (I, H) >> CJ.EQ ((coe, other), ty) = jdg
        val Syn.COE {dir=(r, r'), ty=(u0, ty0), coercee=m} = Syn.out coe
        val () = Assert.paramEq "Coe.CapEq source and target of direction" (r, r')

        (* type *)
        val goalTy = makeType (I @ [(u0, P.DIM)], H) ty0
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r = substSymbol (r, u0) ty0
        val goalTy0 = makeEqTypeIfDifferent (I, H) (ty0r, ty)

        (* eq *)
        val goalEq = makeEq (I, H) ((m, other), ty)
      in
        |>: goalEq >:? goalTy0 >: goalTy #> (I, H, trivial)
      end
  end

  structure Computation =
  struct
    local
      infix $
    in
      fun safeUnfold sign opid m : abt =
        case out m of
           O.POLY (O.CUST (opid',_,_)) $ _ =>
             if Sym.eq (opid, opid') then
               Machine.steps sign Machine.CUBICAL 1 m
                 handle exn => raise Fail ("Impossible failure during safeUnfold: " ^ exnMessage exn)
             else
               m
         | _ => m
    end

    fun Unfold sign opid _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.Unfold"
        val unfold = safeUnfold sign opid o Abt.deepMapSubterms (safeUnfold sign opid)
        val jdg' as (I, H) >> _ = RedPrlSequent.map unfold jdg
        val (goal, hole) = makeGoal @@ jdg'
      in
        |>: goal #> (I, H, hole)
      end

    fun EqHeadExpansion sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqHeadExpansion"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val m' = Machine.eval sign Machine.CUBICAL m
        val goal = makeEq (I, H) ((m', n), ty)
      in
        |>: goal #> (I, H, trivial)
      end
      handle _ => raise E.error [Fpp.text "EqHeadExpansion!"]

    fun EqTypeHeadExpansion sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqTypeHeadExpansion"
        val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
        val ty1' = Machine.eval sign Machine.CUBICAL ty1
        val goal = makeEqType (I, H) (ty1', ty2)
      in
        |>: goal #> (I, H, trivial)
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



  local
    fun checkMainGoal (specGoal, mainGoal) =
      let
        val (I, H) >> jdg = mainGoal
        val (_, H0) >> jdg0 = specGoal
      in
        if CJ.eq (jdg, jdg0) then
          ()
        else 
          raise E.error 
            [Fpp.nest 2 @@ 
              Fpp.vsep 
                [Fpp.text "Conclusions of goal did not match specification:",
                 CJ.pretty Abt.eq TermPrinter.ppTerm jdg,
                 Fpp.text "vs",
                 CJ.pretty Abt.eq TermPrinter.ppTerm jdg0]]
        (* TODO: unify using I, J!! *)
      end

    datatype diff =
       DELETE of hyp
     | UPDATE of hyp * catjdg
     | INSERT of hyp * catjdg

    val diffToString =
      fn DELETE x => "DELETE " ^ Sym.toString x
       | UPDATE (x,_) => "UPDATE " ^ Sym.toString x
       | INSERT (x,_) => "INSERT " ^ Sym.toString x

    fun applyDiffs alpha i xrho deltas H : catjdg Hyps.telescope =
      case deltas of
         [] => H
       | DELETE x :: deltas => applyDiffs alpha i xrho deltas (Hyps.remove x H)
       | UPDATE (x, jdg) :: deltas => applyDiffs alpha i xrho deltas (Hyps.modify x (fn _ => jdg) H)
       | INSERT (x, jdg) :: deltas =>
           let
             val x' = alpha i
             val jdg' = CJ.map (RedPrlAbt.renameVars xrho) jdg
             val xrho' = Var.Ctx.insert xrho x x'
           in
             applyDiffs alpha (i + 1) xrho' deltas (Hyps.snoc H x' jdg')
           end

    fun hypothesesDiff (H0, H1) : diff list =
      let
        val diff01 =
          Hyps.foldr
            (fn (x, jdg0, delta) =>
              case Hyps.find H1 x of
                  SOME jdg1 => if CJ.eq (jdg0, jdg1) then delta else UPDATE (x, jdg1) :: delta
                | NONE => DELETE x :: delta)
            []
            H0
      in
        Hyps.foldr
          (fn (x, jdg1, delta) =>
             case Hyps.find H0 x of
                SOME _ => delta
              | NONE => INSERT (x, jdg1) :: delta)
          diff01
          H1
      end

    (* TODO: This needs to be rewritten; it is probably completely wrong now. *)
    fun instantiateSubgoal alpha (I, H) (subgoalSpec, mainGoalSpec) =
      let
        val (I0, H0) >> jdg0 = subgoalSpec
        val nsyms = List.length I0
        val freshSyms = List.tabulate (List.length I0, fn i => alpha i)
        val I0' = ListPair.map (fn ((_,sigma), v) => (v, sigma)) (I, freshSyms)
        val srho = ListPair.foldl (fn ((u, _), v, rho) => Sym.Ctx.insert rho u (P.ret v)) Sym.Ctx.empty (I, freshSyms)

        val (_, H1) >> _ = mainGoalSpec
        val delta = hypothesesDiff (H1, H0)
        val H0' = applyDiffs alpha nsyms Var.Ctx.empty delta H

        val jdg' = (I @ I0', H0') >> jdg0
        val jdg'' = RedPrlSequent.map (substSymenv srho) jdg'
      in
        jdg''
      end
  in
    fun Lemma sign opid params alpha jdg =
      let
        val _ = RedPrlLog.trace "Lemma"
        val (mainGoalSpec, Lcf.|> (subgoals, validation)) = Sig.resuscitateTheorem sign opid params
        val () = checkMainGoal (mainGoalSpec, jdg)

        val (I as [], H) >> _ = jdg
        val _ = 
          if Hyps.isEmpty H then () else
            raise E.error [Fpp.text "Lemmas must have a categorical judgment as a conclusion"]

        val subgoals' = Lcf.Tl.map (fn subgoalSpec => instantiateSubgoal alpha (I, H) (subgoalSpec, mainGoalSpec)) subgoals
      in
        Lcf.|> (subgoals', validation)
      end
  end

  fun CutLemma sign opid params = 
    let
      val (mainGoalSpec, _) = Sig.resuscitateTheorem sign opid params
      val (I, H) >> catjdg = mainGoalSpec
    in
      Cut catjdg thenl [Lemma sign opid params, fn _ => Lcf.idn]
    end

  fun Exact tm =
    Truth.Witness tm
      orelse_ Term.Exact tm

  local
    val CatJdgSymmetry : Sym.t Tactical.tactic =
      Equality.Symmetry orelse_ TypeEquality.Symmetry

    fun matchGoal f alpha jdg =
      f jdg alpha jdg
  in
    local
      fun StepTrue _ ty =
        case Syn.out ty of
           Syn.PATH_TY _ => Path.True
         | Syn.DFUN _ => DFun.True
         | Syn.DPROD _ => DProd.True
         | Syn.RECORD _ => Record.True
         | _ => raise E.error [Fpp.text "Could not find introduction rule for", TermPrinter.ppTerm ty]

      fun StepEqTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Bool.EqType
         | (Syn.WBOOL, Syn.WBOOL) => WBool.EqType
         | (Syn.NAT, Syn.NAT) => Nat.EqType
         | (Syn.INT, Syn.INT) => Int.EqType
         | (Syn.VOID, Syn.VOID) => Void.EqType
         | (Syn.S1, Syn.S1) => S1.EqType
         | (Syn.DFUN _, Syn.DFUN _) => DFun.EqType
         | (Syn.DPROD _, Syn.DPROD _) => DProd.EqType
         | (Syn.RECORD _, Syn.RECORD _) => Record.EqType
         | (Syn.PATH_TY _, Syn.PATH_TY _) => Path.EqType
         | _ => raise E.error [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

      fun StepEqType sign (ty1, ty2) =
        case (Machine.canonicity sign Machine.NOMINAL ty1, Machine.canonicity sign Machine.NOMINAL ty2) of
           (Machine.REDEX, _) => Computation.EqTypeHeadExpansion sign
         | (_, Machine.REDEX) => CatJdgSymmetry then_ Computation.EqTypeHeadExpansion sign
         | (Machine.CANONICAL, Machine.CANONICAL) => StepEqTypeVal (ty1, ty2)
         | _ => raise E.error [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

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
         | (Syn.LAM _, Syn.LAM _, _) => DFun.Eq
         | (Syn.PAIR _, Syn.PAIR _, _) => DProd.Eq
         | (Syn.TUPLE _, Syn.TUPLE _, _) => Record.Eq
         | (Syn.PATH_ABS _, Syn.PATH_ABS _, _) => Path.Eq
         | _ => raise E.error [Fpp.text "Could not find value equality rule for", TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n, Fpp.text "at type", TermPrinter.ppTerm ty]

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeu (x, y) ((m, n), ty) =
        case (Syn.out m, Syn.out n) of
           (Syn.VAR _, Syn.VAR _) => Equality.Hyp
         | (Syn.WIF _, Syn.WIF _) => WBool.ElimEq
         | (Syn.IF _, Syn.IF _) => Bool.ElimEq
         | (Syn.IF _, _) =>
           (case x of
               Machine.VAR z => Bool.EqElim z
             | _ => raise E.error [Fpp.text "Could not determine critical variable at which to apply Bool elimination"])
         | (_, Syn.IF _) =>
           (case y of
               Machine.VAR z => CatJdgSymmetry then_ Bool.EqElim z
             | _ => raise E.error [Fpp.text "Could not determine critical variable at which to apply Bool elimination"])
         | (Syn.NAT_REC _, Syn.NAT_REC _) => Nat.ElimEq
         | (Syn.S1_REC _, Syn.S1_REC _) => S1.ElimEq
         | (Syn.APP _, Syn.APP _) => DFun.AppEq
         | (Syn.FST _, Syn.FST _) => DProd.FstEq
         | (Syn.SND _, Syn.SND _) => DProd.SndEq
         | (Syn.PROJ _, Syn.PROJ _) => Record.ProjEq
         | (Syn.PATH_APP (_, P.VAR _), Syn.PATH_APP (_, P.VAR _)) => Path.AppEq
         | _ => raise E.error [Fpp.text "Could not find neutral equality rule for", TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n, Fpp.text "at type", TermPrinter.ppTerm ty]

      fun StepEqNeuExpand ty =
        case Syn.out ty of
           Syn.DPROD _ => DProd.Eta
         | Syn.DFUN _ => DFun.Eta
         | Syn.PATH_TY _ => Path.Eta
         | Syn.RECORD _ => Record.Eta
         | _ => raise E.error [Fpp.text "Could not expand neutral term of type", TermPrinter.ppTerm ty]


      structure HCom =
      struct
        open HCom

        val AutoEqL = CapEqL orelse_ TubeEqL orelse_ Eq

        (* Try all the hcom rules.
         * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
        val AutoEqLR =
          CapEqL
            orelse_ (CatJdgSymmetry then_ HCom.CapEqL)
            orelse_ HCom.TubeEqL
            orelse_ (CatJdgSymmetry then_ HCom.TubeEqL)
            orelse_ HCom.Eq
      end

      structure Coe =
      struct
       open Coe

       val CapEqR = CatJdgSymmetry then_ CapEqL
       val AutoEqLR = CapEqL orelse_ CapEqR orelse_ Eq
       val AutoEqL = CapEqL orelse_ Eq
       val AutoEqR = CapEqR orelse_ Eq
      end

      (* these are special rules which are not beta or eta,
       * and we have to check them against the neutral terms.
       * it looks nicer to list all of them here. *)
      fun StepEqStuck _ ((m, n), ty) canonicity =
        case (Syn.out m, Syn.out n) of
           (Syn.HCOM _, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.HCOM _, _) => HCom.AutoEqL
         | (_, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.COE _, Syn.COE _) => Coe.AutoEqLR
         | (Syn.COE _, _) => Coe.AutoEqL
         | (_, Syn.COE _) => Coe.AutoEqR
         | (Syn.PATH_APP (_, P.APP _), _) => Path.AppConstCompute
         | (_, Syn.PATH_APP (_, P.APP _)) => CatJdgSymmetry then_ Path.AppConstCompute
         | _ =>
           (case canonicity of
               (Machine.NEUTRAL x, Machine.NEUTRAL y) => StepEqNeu (x, y) ((m, n), ty)
             | (Machine.NEUTRAL _, Machine.CANONICAL) => StepEqNeuExpand ty
             | (Machine.CANONICAL, Machine.NEUTRAL _) => CatJdgSymmetry then_ StepEqNeuExpand ty)

      fun StepEq sign ((m, n), ty) =
        case (Machine.canonicity sign Machine.NOMINAL m, Machine.canonicity sign Machine.NOMINAL n) of
           (Machine.REDEX, _) => Computation.EqHeadExpansion sign
         | (_, Machine.REDEX) => CatJdgSymmetry then_ Computation.EqHeadExpansion sign
         | (Machine.CANONICAL, Machine.CANONICAL) => StepEqVal ((m, n), ty)
         | canonicity => StepEqStuck sign ((m, n), ty) canonicity

      fun StepSynth _ m =
        case Syn.out m of
           Syn.VAR _ => Synth.Hyp
         | Syn.APP _ => Synth.App
         | Syn.S1_REC _ => Synth.S1Rec
         | Syn.WIF _ => Synth.WIf
         | Syn.PATH_APP _ => Synth.PathApp
         | Syn.FST _ => Synth.Fst
         | Syn.SND _ => Synth.Snd
         | _ => raise E.error [Fpp.text "Could not find suitable type synthesis rule for", TermPrinter.ppTerm m]

      fun StepJdg sign = matchGoal
        (fn _ >> CJ.TRUE ty => StepTrue sign ty
          | _ >> CJ.EQ_TYPE tys => StepEqType sign tys
          | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
          | _ >> CJ.SYNTH m => StepSynth sign m
          | MATCH _ => Misc.MatchOperator
          | MATCH_RECORD _ => Record.MatchRecord
          | DIM_SUBST _ => Misc.DimSubst)


      fun isWfJdg (CJ.TRUE _) = false
        | isWfJdg _ = true

      structure HypsUtil = TelescopeUtil (Hyps)

      fun FindHyp alpha ((I, H) >> jdg) =
        if isWfJdg jdg then
          case HypsUtil.search H (fn jdg' => CJ.eq (jdg, jdg')) of
             SOME (lbl, _) => Hyp.Project lbl alpha ((I, H) >> jdg)
           | NONE => raise E.error [Fpp.text "Could not find suitable hypothesis"]
        else
          raise E.error [Fpp.text "Non-deterministic tactics can only be run on auxiliary goals"]
    in
      fun AutoStep sign alpha jdg = 
        StepJdg sign alpha jdg
          handle exn => 
            FindHyp alpha jdg
            handle _ => raise exn
    end

    local
      fun StepTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.WBOOL => WBool.Elim
         | Syn.NAT => Nat.Elim
         | Syn.VOID => Void.Elim
         | Syn.S1 => S1.Elim
         | Syn.DFUN _ => DFun.Elim
         | Syn.DPROD _ => DProd.Elim
         | Syn.PATH_TY _ => Path.Elim
         | _ => raise E.error [Fpp.text "Could not find suitable elimination rule for", TermPrinter.ppTerm ty]

      fun StepEq ty =
        case Syn.out ty of
           Syn.BOOL => Bool.EqElim
         | _ => raise E.error [Fpp.text "Could not find suitable elimination rule for", TermPrinter.ppTerm ty]

      fun StepJdg _ z alpha jdg =
        let
          val (_, H) >> catjdg = jdg
        in
          case lookupHyp H z of
             CJ.TRUE hyp =>
              (case catjdg of
                  CJ.TRUE _ => StepTrue hyp z alpha jdg
                | CJ.EQ _ => StepEq hyp z alpha jdg
                | _ => raise E.error [Fpp.text ("Could not find suitable elimination rule [TODO, display information]")])
           | _ => raise E.error [Fpp.text "Could not find suitable elimination rule"]
        end
    in
      val Elim = StepJdg
    end

  end
end
