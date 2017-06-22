functor Refiner (Sig : MINI_SIGNATURE) : REFINER =
struct
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
  infix 2 >> >: >:+ $$ $# // \ @>
  infix orelse_

  structure Equality =
  struct
    fun Hyp alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.Hyp"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = assertVarEq (x, y)
        val catjdg = lookupHyp H x
        val ty' =
          case catjdg of
             CJ.TRUE ty => ty
           | _ => raise E.error [E.% "Equality.Hyp: expected truth hypothesis"]
      in
        (* If the types are identical, there is no need to create a new subgoal (which would amount to proving that 'ty' is a type).
           This is because the semantics of sequents is that by assuming that something is a member of a 'ty', we have
           automatically assumed that 'ty' is a type. *)
        if Syn.Tm.eq (ty, ty') then
          T.empty #> (I, H, trivial)
        else
          let
            val (goalTy, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty, ty')
          in
            T.empty >: goalTy #> (I, H, trivial)
          end
      end
      handle Bind =>
        raise E.error [E.% "Expected variable-equality sequent"]

    fun Symmetry alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val (goal, hole) = makeGoal @@ (I, H) >> CJ.EQ ((n, m), ty)
      in
        T.empty >: goal
          #> (I, H, trivial)
      end
  end

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COE {dir=(r0, r'0), ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=(r1, r'1), ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = assertParamEq "Coe.Eq source of direction" (r0, r1)
        val () = assertParamEq "Coe.Eq target of direction" (r'0, r'1)

        val ty01 = substSymbol (r'0, u) ty0u
        val (goalTy1, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty01, ty)

        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u) ty0u
        val ty1w = substSymbol (P.ret w, v) ty1v
        val (goalTy, _) = makeGoal @@ (I @ [(w, P.DIM)], H) >> CJ.EQ_TYPE (ty0w, ty1w)

        val ty00 = substSymbol (r0, u) ty0u
        val (goalCoercees, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), ty00)
      in
        T.empty >: goalTy1 >: goalTy >: goalCoercees #> (I, H, trivial)
      end

    fun CapEqL alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.CapEq"
        val (I, H) >> CJ.EQ ((coe, other), ty) = jdg
        val Syn.COE {dir=(r, r'), ty=(u, tyu), coercee=m} = Syn.out coe
        val () = assertParamEq "Coe.CapEq source and target of direction" (r, r')

        val ty0 = substSymbol (r, u) tyu
        val (goalTy0, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty0, ty)

        val (goalTy, _) = makeGoal @@ (I @ [(u, P.DIM)], H) >> CJ.TYPE tyu
        val (goalEq, _) = makeGoal @@ (I, H) >> CJ.EQ ((m, other), ty)
      in
        T.empty >: goalTy0 >: goalTy >: goalEq #> (I, H, trivial)
      end

    fun CapEqR alpha = catJdgFlipWrapper CapEqL alpha

    (* Try all the fcom rules.
     * Note that the EQ rule is invertible only when the cap rule fails. *)
    val AutoEqLR = CapEqL orelse_ CapEqR orelse_ Eq
    val AutoEqL = CapEqL orelse_ Eq
    val AutoEqR = CapEqR orelse_ Eq
  end

  structure Hyp =
  struct
    fun Project z alpha jdg =
      let
        val _ = RedPrlLog.trace "Hyp.Project"
        val (I, H) >> catjdg = jdg
        val catjdg' = lookupHyp H z
      in
        if CJ.eq (catjdg, catjdg') then
          T.empty #> (I, H, Syn.into (Syn.VAR (z, CJ.synthesis catjdg)))
        else
          raise E.error [E.% "Hypothesis does not match goal"]
      end
      handle Bind =>
        raise E.error [E.% "Expected sequent judgment"]
  end

  structure TypeEquality =
  struct
    fun Symmetry alpha jdg =
    let
      val _ = RedPrlLog.trace "Equality.Symmetry"
      val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
      val (goal, hole) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty2, ty1)
    in
      T.empty >: goal
        #> (I, H, trivial)
    end
  end

  structure Truth =
  struct
    fun Witness tm alpha jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> CJ.TRUE ty = jdg
        val (goal, _) = makeGoal @@ (I, H) >> CJ.MEM (tm, ty)
      in
        T.empty >: goal
          #> (I, H, tm)
      end
      handle Bind =>
        raise E.error [E.% @@ "Expected truth sequent but got " ^ J.toString jdg]
  end

  structure Synth =
  struct
    fun FromWfHyp z alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromWfHyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val CJ.EQ ((a, b), ty) = Hyps.lookup H z
      in
        if Abt.eq (a, tm) orelse Abt.eq (b, tm) then
          T.empty #> (I, H, ty)
        else
          raise Fail "Did not match"
      end

    fun Hyp alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Hyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val CJ.TRUE a = Hyps.lookup H z
      in
        T.empty #> (I, H, a)
      end

    fun If alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.If"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.IF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val (goal, _) = makeGoal @@ (I, H) >> CJ.MEM (tm, cm)
      in
        T.empty >: goal
          #> (I, H, cm)
      end

    fun S1Elim alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.S1Elim"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.S1_ELIM ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val (goal, _) = makeGoal @@ (I, H) >> CJ.MEM (tm, cm)
      in
        T.empty >: goal
          #> (I, H, cm)
      end

    fun Ap alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Ap"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.AP (m, n) = Syn.out tm
        val (goalDFun, holeDFun) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalDom, holeDom) = makeGoal @@ MATCH (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeGoal @@ MATCH (O.MONO O.DFUN, 1, holeDFun, [], [n])
        val (goalN, _) = makeGoal @@ (I, H) >> CJ.MEM (n, holeDom)
      in
        T.empty >: goalDFun >: goalDom >: goalCod >: goalN
          #> (I, H, holeCod)
      end

    fun PathAp alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.PathAp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.PATH_AP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalLine, holeLine) = makeGoal @@ MATCH (O.MONO O.PATH_TY, 0, holePathTy, [r], [])
        val psi = T.empty >: goalPathTy >: goalLine
      in
        T.empty >: goalPathTy >: goalLine
          #> (I, H, holeLine)
      end

    fun Fst alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Fst"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.FST m = Syn.out tm
        val (goalTy, holeTy) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalA, holeA) = makeGoal @@ MATCH (O.MONO O.DPROD, 0, holeTy, [], [])
      in
        T.empty >: goalTy >: goalA
          #> (I, H, holeA)
      end

    fun Snd alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Snd"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.SND m = Syn.out tm
        val (goalTy, holeTy) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalB, holeB) = makeGoal @@ MATCH (O.MONO O.DPROD, 1, holeTy, [], [Syn.into @@ Syn.FST m])
      in
        T.empty >: goalTy >: goalB
          #> (I, H, holeB)
      end
  end

  structure Match =
  struct
    fun MatchOperator alpha jdg =
      let
        val _ = RedPrlLog.trace "Match.MatchOperator"
        val MATCH (th, k, tm, ps, ms) = jdg

        val Abt.$ (th', args) = Abt.out tm
        val true = Abt.O.eq Sym.eq (th, th')

        val (vls, _) = Abt.O.arity th
        val (us, xs) \ arg = List.nth (args, k)
        val srho = ListPair.foldrEq (fn (u,p,rho) => Sym.Ctx.insert rho u p) Sym.Ctx.empty (us, ps)
        val vrho = ListPair.foldrEq (fn (x,m,rho) => Var.Ctx.insert rho x m) Var.Ctx.empty (xs, ms)

        val arg' = substSymenv srho (substVarenv vrho arg)
      in
        Lcf.|> (T.empty, abtToAbs arg')
      end
      handle _ =>
        raise E.error [E.% "MATCH judgment failed to unify"]
  end

  structure Equality =
  struct
    fun Hyp alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.Hyp"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = assertVarEq (x, y)
        val catjdg = lookupHyp H x
        val ty' =
          case catjdg of
             CJ.TRUE ty => ty
           | _ => raise E.error [E.% "Equality.Hyp: expected truth hypothesis"]
      in
        (* If the types are identical, there is no need to create a new subgoal (which would amount to proving that 'ty' is a type).
           This is because the semantics of sequents is that by assuming that something is a member of a 'ty', we have
           automatically assumed that 'ty' is a type. *)
        if Syn.Tm.eq (ty, ty') then
          T.empty #> (I, H, trivial)
        else
          let
            val (goalTy, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty, ty')
          in
            T.empty >: goalTy #> (I, H, trivial)
          end
      end
      handle Bind =>
        raise E.error [E.% "Expected variable-equality sequent"]

    fun Symmetry alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val (goal, hole) = makeGoal @@ (I, H) >> CJ.EQ ((n, m), ty)
      in
        T.empty >: goal
          #> (I, H, trivial)
      end
  end

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COE {dir=(r0, r'0), ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=(r1, r'1), ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = assertParamEq "Coe.Eq source of direction" (r0, r1)
        val () = assertParamEq "Coe.Eq target of direction" (r'0, r'1)

        val ty01 = substSymbol (r'0, u) ty0u
        val (goalTy1, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty01, ty)

        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u) ty0u
        val ty1w = substSymbol (P.ret w, v) ty1v
        val (goalTy, _) = makeGoal @@ (I @ [(w, P.DIM)], H) >> CJ.EQ_TYPE (ty0w, ty1w)

        val ty00 = substSymbol (r0, u) ty0u
        val (goalCoercees, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), ty00)
      in
        T.empty >: goalTy1 >: goalTy >: goalCoercees #> (I, H, trivial)
      end

    fun CapEqL alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.CapEq"
        val (I, H) >> CJ.EQ ((coe, other), ty) = jdg
        val Syn.COE {dir=(r, r'), ty=(u, tyu), coercee=m} = Syn.out coe
        val () = assertParamEq "Coe.CapEq source and target of direction" (r, r')

        val ty0 = substSymbol (r, u) tyu
        val (goalTy0, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty0, ty)

        val (goalTy, _) = makeGoal @@ (I @ [(u, P.DIM)], H) >> CJ.TYPE tyu
        val (goalEq, _) = makeGoal @@ (I, H) >> CJ.EQ ((m, other), ty)
      in
        T.empty >: goalTy0 >: goalTy >: goalEq #> (I, H, trivial)
      end

    fun CapEqR alpha = catJdgFlipWrapper CapEqL alpha

    (* Try all the fcom rules.
     * Note that the EQ rule is invertible only when the cap rule fails. *)
    val AutoEqLR = CapEqL orelse_ CapEqR orelse_ Eq
    val AutoEqL = CapEqL orelse_ Eq
    val AutoEqR = CapEqR orelse_ Eq
  end

  structure Computation =
  struct
    local
      open Machine.S.Cl infix <: $
    in
      (* This should be safe---but it is not ideal, because we have to force the deferred
       * substitutions in order to determine whether it is safe to take a step. *)
      fun safeStep sign (st as (mode, cl, stk)) : abt Machine.S.state option =
        let
          val m = force cl
        in
          case (out m, Machine.canonicity sign m) of
             (_, Machine.CANONICAL) => Machine.next sign st
           | (O.POLY (O.CUST _) $ _, _) => Machine.next sign st
           | (th $ _, _) =>
               if List.exists (fn (_, sigma) => sigma = P.DIM) @@ Abt.O.support th then
                 raise Fail ("Unsafe step: " ^ TermPrinter.toString m)
               else
                 Machine.next sign st
           | _ => NONE
        end

      fun safeEval sign st =
        case safeStep sign st of
           NONE => st
         | SOME st' => safeEval sign st'

      fun safeUnfold sign opid m =
        case out m of
           O.POLY (O.CUST (opid',_,_)) $ _ =>
             if Sym.eq (opid, opid') then
               Machine.unload sign (Option.valOf (safeStep sign (Machine.load m)))
                 handle _ => raise Fail "Impossible failure during safeUnfold" (* please put better error message here; should never happen anyway *)
             else
               m
         | _ => m
    end

    fun Unfold sign opid alpha jdg =
      let
        val _ = RedPrlLog.trace "Computation.Unfold"
        val unfold = safeUnfold sign opid o Abt.deepMapSubterms (safeUnfold sign opid)
        val jdg' as (I, H) >> _ = RedPrlSequent.map unfold jdg
        val (goal, hole) = makeGoal @@ jdg'
      in
        T.empty >: goal #> (I, H, hole)
      end

    fun EqHeadExpansion sign alpha jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqHeadExpansion"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Abt.$ (theta, _) = Abt.out m
        val m' = Machine.unload sign (safeEval sign (Machine.load m))
        val (goal, _) = makeGoal @@ (I, H) >> CJ.EQ ((m', n), ty)
      in
        T.empty >: goal
          #> (I, H, trivial)
      end
      handle _ => raise E.error [E.% "EqHeadExpansion!"]

    fun EqTypeHeadExpansion sign alpha jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqTypeHeadExpansion"
        val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
        val Abt.$ (theta, _) = Abt.out ty1
        val ty1' = Machine.unload sign (safeEval sign (Machine.load ty1))
        val (goal, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty1', ty2)
        in
          T.empty >: goal
            #> (I, H, trivial)
        end
  end

  fun Cut catjdg alpha jdg =
    let
      val _ = RedPrlLog.trace "Cut"
      val (I, H) >> catjdg' = jdg
      val z = alpha 0
      val tau = CJ.synthesis catjdg
      val (goal1, hole1) = makeGoal @@ (I, H @> (z, catjdg)) >> catjdg'
      val (goal2, hole2) = makeGoal @@ (I, H) >> catjdg
    in
      T.empty >: goal1 >: goal2
        #> (I, H, substVar (hole2, z) hole1)
    end


  local
    fun checkHyp H x jdg0 =
      case Hyps.find H x of
         SOME jdg =>
           if CJ.eq (jdg, jdg0) then () else
             raise E.error [E.% ("Hypothesis " ^ Sym.toString x ^ " did not match specification")]
       | _ => raise E.error [E.% ("Could not find hypothesis " ^ Sym.toString x)]

    fun checkMainGoal (specGoal, mainGoal) =
      let
        val (I, H) >> jdg = mainGoal
        val (J, H0) >> jdg0 = specGoal
      in
        if CJ.eq (jdg, jdg0) then () else raise E.error [E.% "Conclusions of goal did not match specification"];
        Hyps.foldl (fn (x, j, _) => checkHyp H x j) () H0
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
                SOME jdg0 => delta
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
        val I0' = ListPair.map (fn ((u,sigma), v) => (v, sigma)) (I, freshSyms)
        val srho = ListPair.foldl (fn ((u, _), v, rho) => Sym.Ctx.insert rho u (P.ret v)) Sym.Ctx.empty (I, freshSyms)

        val (I1, H1) >> jdg1 = mainGoalSpec
        val delta = hypothesesDiff (H1, H0)
        val H0' = applyDiffs alpha nsyms Var.Ctx.empty delta H

        val jdg' = (I @ I0', H0') >> jdg0
        val jdg'' = RedPrlSequent.map (substSymenv srho) jdg'
      in
        jdg''
      end
  in
    fun Lemma sign opid params args alpha jdg =
      let
        val _ = RedPrlLog.trace "Lemma"
        val (mainGoalSpec, state as Lcf.|> (subgoals, validation)) = Sig.resuscitateTheorem sign opid params args
        val _ = checkMainGoal (mainGoalSpec, jdg)

        val (I, H) >> _ = jdg

        val subgoals' = Lcf.Tl.map (fn subgoalSpec => instantiateSubgoal alpha (I, H) (subgoalSpec, mainGoalSpec)) subgoals
      in
        Lcf.|> (subgoals', validation)
      end
  end

  local
    fun matchGoal f alpha jdg =
      f jdg alpha jdg
  in
    local
      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.PATH_TY _ => Path.True
         | Syn.DFUN _ => DFun.True
         | Syn.DPROD _ => DProd.True
         | _ => raise E.error [E.% "Could not find introduction rule for", E.! ty]

      fun StepEqTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Bool.EqType
         | (Syn.S_BOOL, Syn.S_BOOL) => StrictBool.EqType
         | (Syn.VOID, Syn.VOID) => Void.EqType
         | (Syn.S1, Syn.S1) => S1.EqType
         | (Syn.DFUN _, Syn.DFUN _) => DFun.EqType
         | (Syn.DPROD _, Syn.DPROD _) => DProd.EqType
         | (Syn.PATH_TY _, Syn.PATH_TY _) => Path.EqType
         | _ => raise E.error [E.% "Could not find type equality rule for", E.! ty1, E.% "and", E.! ty2]

      fun StepEqType sign (ty1, ty2) =
        case (Machine.canonicity sign ty1, Machine.canonicity sign ty2) of
           (Machine.CANONICAL, Machine.CANONICAL) => StepEqTypeVal (ty1, ty2)
         | (Machine.REDEX, _) => Computation.EqTypeHeadExpansion sign
         | (_, Machine.REDEX) => TypeEquality.Symmetry
         | _ => raise E.error [E.% "Could not find type equality rule for", E.! ty1, E.% "and", E.! ty2]

      (* equality of canonical forms *)
      fun StepEqVal ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.TT, Syn.TT, Syn.BOOL) => Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Bool.EqFF
         | (Syn.FCOM _, Syn.FCOM _, Syn.BOOL) => Bool.EqFCom
         | (Syn.TT, Syn.TT, Syn.S_BOOL) => StrictBool.EqTT
         | (Syn.FF, Syn.FF, Syn.S_BOOL) => StrictBool.EqFF
         | (Syn.BASE, Syn.BASE, Syn.S1) => S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => S1.EqLoop
         | (Syn.FCOM _, Syn.FCOM _, Syn.S1) => S1.EqFCom
         | (Syn.LAM _, Syn.LAM _, _) => DFun.Eq
         | (Syn.PAIR _, Syn.PAIR _, _) => DProd.Eq
         | (Syn.PATH_ABS _, Syn.PATH_ABS _, _) => Path.Eq
         | _ => raise E.error [E.% "Could not find value equality rule for", E.! m, E.% "and", E.! n, E.% "at type", E.! ty]

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeu (x, y) ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.VAR _, Syn.VAR _, _) => Equality.Hyp
         | (Syn.IF _, Syn.IF _, _) => Bool.ElimEq
         | (Syn.S_IF _, Syn.S_IF _, _) => StrictBool.ElimEq
         | (Syn.S_IF _, _, _) =>
           (case x of
               Machine.VAR z => StrictBool.EqElim z
             | _ => raise E.error [E.% "Could not determine critical variable at which to apply sbool elimination"])
         | (_, Syn.S_IF _, _) => Equality.Symmetry
         | (Syn.S1_ELIM _, Syn.S1_ELIM _, _) => S1.ElimEq
         | (Syn.AP _, Syn.AP _, _) => DFun.ApEq
         | (Syn.FST _, Syn.FST _, _) => DProd.FstEq
         | (Syn.SND _, Syn.SND _, _) => DProd.SndEq
         | (Syn.PATH_AP (_, P.VAR _), Syn.PATH_AP (_, P.VAR _), _) => Path.ApEq
         | (_, Syn.PATH_AP (_, P.APP _), _) => Equality.Symmetry
         | _ => raise E.error [E.% "Could not find neutral equality rule for", E.! m, E.% "and", E.! n, E.% "at type", E.! ty]

      fun StepEqNeuExpand (m, ty) =
        case (Syn.out m, Syn.out ty) of
           (_, Syn.DPROD _) => DProd.Eta
         | (_, Syn.DFUN _) => DFun.Eta
         | (_, Syn.PATH_TY _) => Path.Eta
         | _ => raise E.error [E.% "Could not expand neutral term of type", E.! ty]

      fun StepEqCanonicity sign ((m, n), ty) =
        case (Machine.canonicity sign m, Machine.canonicity sign n) of
           (Machine.REDEX, _) => Computation.EqHeadExpansion sign
         | (Machine.CANONICAL, Machine.CANONICAL) => StepEqVal ((m, n), ty)
         | (Machine.NEUTRAL x, Machine.NEUTRAL y) => StepEqNeu (x, y) ((m, n), ty)
         | (Machine.NEUTRAL _, Machine.CANONICAL) => StepEqNeuExpand (m, ty)
         | _ => Equality.Symmetry

      fun StepEq sign ((m, n), ty) =
        case (Syn.out m, Syn.out n) of
           (Syn.HCOM _, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.HCOM _, _) => HCom.AutoEqL
         | (_, Syn.HCOM _) => HCom.AutoEqLR
         | (Syn.COE _, Syn.COE _) => Coe.AutoEqLR
         | (Syn.COE _, _) => Coe.AutoEqL
         | (_, Syn.COE _) => Coe.AutoEqR
         | (Syn.PATH_AP (_, P.APP _), _) => Path.ApConstCompute
         | (_, Syn.PATH_AP (_, P.APP _)) => Equality.Symmetry
         | _ => StepEqCanonicity sign ((m, n), ty)

      fun StepSynth sign m =
        case Syn.out m of
           Syn.VAR _ => Synth.Hyp
         | Syn.AP _ => Synth.Ap
         | Syn.S1_ELIM _ => Synth.S1Elim
         | Syn.IF _ => Synth.If
         | Syn.PATH_AP _ => Synth.PathAp
         | Syn.FST _ => Synth.Fst
         | Syn.SND _ => Synth.Snd
         | _ => raise E.error [E.% "Could not find suitable type synthesis rule for", E.! m]

      fun StepJdg sign = matchGoal
        (fn _ >> CJ.TRUE ty => StepTrue sign ty
          | _ >> CJ.EQ_TYPE tys => StepEqType sign tys
          | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
          | _ >> CJ.SYNTH m => StepSynth sign m
          | MATCH _ => Match.MatchOperator)


      fun isWfJdg (CJ.TRUE _) = false
        | isWfJdg _ = true

      structure HypsUtil = TelescopeUtil (Hyps)

      fun FindHyp alpha ((I, H) >> jdg) =
        if isWfJdg jdg then
          case HypsUtil.search H (fn jdg' => CJ.eq (jdg, jdg')) of
             SOME (lbl, _) => Hyp.Project lbl alpha ((I, H) >> jdg)
           | NONE => raise E.error [E.% "Could not find suitable hypothesis"]
        else
          raise E.error [E.% "Non-deterministic tactics can only be run on auxiliary goals"]
    in
      fun AutoStep sign = StepJdg sign orelse_ FindHyp
    end

    local
      fun StepTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.S_BOOL => StrictBool.Elim
         | Syn.VOID => Void.Elim
         | Syn.S1 => S1.Elim
         | Syn.DFUN _ => DFun.Elim
         | Syn.DPROD _ => DProd.Elim
         | _ => raise E.error [E.% "Could not find suitable elimination rule for", E.! ty]

      fun StepEq ty =
        case Syn.out ty of
           Syn.S_BOOL => StrictBool.EqElim
         | _ => raise E.error [E.% "Could not find suitable elimination rule for", E.! ty]

      fun StepJdg sign z alpha jdg =
        let
          val (I, H) >> catjdg = jdg
        in
          case lookupHyp H z of
             CJ.TRUE hyp =>
              (case catjdg of
                  CJ.TRUE _ => StepTrue hyp z alpha jdg
                | CJ.EQ _ => StepEq hyp z alpha jdg
                | _ => raise E.error [E.% ("Could not find suitable elimination rule for " ^ CJ.toString catjdg)])
           | _ => raise E.error [E.% "Could not find suitable elimination rule"]
        end
    in
      val Elim = StepJdg
    end

  end
end
