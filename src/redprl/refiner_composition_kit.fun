functor RefinerCompositionKit (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = CJ.jdg
  type opid = Sig.opid

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix orelse_

  structure Restriction :
  sig
    (* This structure used to provide functions that automate the
       restriction judgement rules given in "Dependent Cubical
       Realizability", page 46.

       On 2017/06/14, favonia implemented a function to handle
       all cases.
     *)

    (* Restrict a judgement (as the goal) by a list of equations.
     * Returns NONE if the resulting judgement is vacuously true.
     *)
    val restrict : (param * param) list -> (abt -> abt) option
  end
  =
  struct
    (* A helper function which does substitution in a parameter. *)
    fun substSymInParam (r, v) = P.bind (fn u => if Sym.eq (u, v) then r else P.ret u)

    (* precondition: all parameters in equations are of sorts `DIM` *)
    fun restrict' [] f = SOME f
      | restrict' ((P.APP d1, P.APP d2) :: eqs) f =
          (* The following line is correct because we only have constants
           * (DIM0 and DIM1). If in the future we want to have connections
           * or other stuff, then a real unification algorithm might be needed.
           *)
          if P.Sig.eq (fn _ => true) (d1, d2) then restrict' eqs f else NONE
      | restrict' ((r1 as P.VAR v1, r2) :: eqs) f =
          if P.eq Sym.eq (r1, r2) then restrict' eqs f else substAndRestrict' (r2, v1) eqs f
      | restrict' ((r1, P.VAR v2) :: eqs) f =
          substAndRestrict' (r1, v2) eqs f

    and substAndRestrict' rv eqs f =
          restrict'
            (List.map (fn (r, r') => (substSymInParam rv r, substSymInParam rv r')) eqs)
          (substSymbol rv o f)

    fun restrict eqs = restrict' eqs (fn x => x)
  end
  (* adding some helper functions *)
  structure Restriction =
  struct
    open Restriction

    fun restrictJdg eqs jdg = Option.map (fn f => Seq.map f jdg) (restrict eqs)

    fun makeEq eqs (I, H) ((m, n), (ty, l, k)) =
      Option.map
        (fn f => makeEqWith f (I, H) ((m, n), (ty, l, k)))
        (restrict eqs)

    fun makeEqIfDifferent eqs (I, H) ((m, n), (ty, l, k)) =
      Option.mapPartial
        (fn f =>
          if Abt.eq (f m, f n) then NONE
          else SOME @@ makeEqWith f (I, H) ((m, n), (ty, l, k)))
        (restrict eqs)

    fun makeMem eqs (I, H) (m, (ty, l, k)) =
      makeEq eqs (I, H) ((m, m), (ty, l, k))

    fun makeEqType eqs (I, H) ((a, b), l, k) =
      Option.map
        (fn f => makeEqTypeWith f (I, H) ((a, b), l, k))
        (restrict eqs)

    fun makeEqTypeIfDifferent eqs (I, H) ((a, b), l, k) =
      Option.mapPartial
        (fn f =>
          if Abt.eq (f a, f b) then NONE
          else SOME @@ makeEqTypeWith f (I, H) ((a, b), l, k))
        (restrict eqs)

    fun makeTrue eqs default (I, H) (a, l, k) =
      case restrict eqs of
        NONE => (NONE, default)
      | SOME f =>
          let
            val (goal, hole) = makeTrueWith f (I, H) (a, l, k)
          in
            (SOME goal, hole)
          end
  end

  (* code shared by Com, HCom and FCom. *)
  structure ComKit =
  struct
    (* todo: optimizing the restriction process even further. *)
    (* todo: pre-restrict r=0, r=1, 0=r and 1=r. *)
    (* todo: try to reduce substitution. *)

    (* Produce the list of goals requiring that tube aspects agree with each other.
         forall i <= j.
           N_i = P_j in A [Psi, y | r_i = r_i', r_j = r_j']
     *)
    fun alphaRenameTubes w = List.map (fn (eq, (u, tube)) => (eq, substSymbol (P.ret w, u) tube))
    fun enumInterExceptDiag f =
      let
        fun enum ([], []) = []
          | enum ((t0 :: ts0), (_ :: ts1)) = List.mapPartial (fn t1 => f (t0, t1)) ts1 :: enum (ts0, ts1)
          | enum _ = E.raiseError @@ E.IMPOSSIBLE @@ Fpp.text "enumInterExceptDiag: inputs are of different lengths"
      in
        List.concat o enum
      end

    local
      fun genTubeGoals' (I, H) ((tubes0, tubes1), (ty, l, k)) =
        ListPairUtil.mapPartialEq
          (fn ((eq, t0), (_, t1)) => Restriction.makeEq [eq] (I, H) ((t0, t1), (ty, l, k)))
          (tubes0, tubes1)
      fun genInterTubeGoalsExceptDiag' (I, H) ((tubes0, tubes1), (ty, l, k)) =
        enumInterExceptDiag
          (fn ((eq0, t0), (eq1, t1)) => Restriction.makeEqIfDifferent [eq0, eq1] (I, H) ((t0, t1), (ty, l, k)))
          (tubes0, tubes1)
    in
      fun genInterTubeGoals (I, H) w ((tubes0, tubes1), (ty, l, k)) =
        let
          val tubes0 = alphaRenameTubes w tubes0
          val tubes1 = alphaRenameTubes w tubes1

          val goalsOnDiag = genTubeGoals' (I @ [(w,P.DIM)], H) ((tubes0, tubes1), (ty, l, k))
          val goalsNotOnDiag = genInterTubeGoalsExceptDiag' (I @ [(w,P.DIM)], H) ((tubes0, tubes1), (ty, NONE, K.top))
        in
          goalsOnDiag @ goalsNotOnDiag
        end
    end

    (* Produce the list of goals requiring that tube aspects agree with the cap.
         forall i.
           M = N_i<r/y> in A [Psi | r_i = r_i']
     *)
    fun genCapTubeGoalsIfDifferent (I, H) ((cap, (r, tubes)), (ty, l, k)) =
      List.mapPartial
        (fn (eq, (u, tube)) =>
          Restriction.makeEqIfDifferent [eq] (I, H) ((cap, substSymbol (r, u) tube), (ty, l, k)))
        tubes

    (* Note that this does not check whether the 'ty' is a base type.
     * It's caller's responsibility to check whether the type 'ty'
     * recognizes FCOM as values. *)
    fun EqFComDelegate alpha (I, H) args0 args1 (ty, l, k) =
      let
        val {dir=dir0, cap=cap0, tubes=tubes0} = args0
        val {dir=dir1, cap=cap1, tubes=tubes1} = args1
        val () = Assert.dirEq "EqFComDelegator direction" (dir0, dir1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = Assert.equationsEq "EqFComDelegator equations" (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "EqFComDelegator tautology checking" eqs0

        val goalCap = makeEq (I, H) ((cap0, cap1), (ty, l, k))

        val w = alpha 0
      in
        |>: goalCap
         >:+ genInterTubeGoals (I, H) w ((tubes0, tubes1), (ty, l, k))
         >:+ genCapTubeGoalsIfDifferent (I, H) ((cap0, (#1 dir0, tubes0)), (ty, NONE, K.top))
        #> (I, H, trivial)
      end
  end

  structure HCom =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val k = K.meet (k, K.HCOM)
        (* these operations could be expensive *)
        val Syn.HCOM {dir=dir0, ty=ty0, cap=cap0, tubes=tubes0} = Syn.out lhs
        val Syn.HCOM {dir=dir1, ty=ty1, cap=cap1, tubes=tubes1} = Syn.out rhs
        val () = Assert.dirEq "HCom.Eq direction" (dir0, dir1)

        (* equations *)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = Assert.equationsEq "HCom.Eq equations" (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "HCom.Eq tautology checking" eqs0

        (* type *)
        val goalTy = makeEqTypeIfDifferent (I, H) ((ty0, ty1), l, k)
        val goalTy0 = makeEqTypeIfDifferent (I, H) ((ty0, ty), l, k)

        (* cap *)
        val goalCap = makeEq (I, H) ((cap0, cap1), (ty, l, k))

        val w = alpha 0
      in
        |>: goalCap
         >:+ ComKit.genInterTubeGoals (I, H) w ((tubes0, tubes1), (ty0, l, k))
         >:+ ComKit.genCapTubeGoalsIfDifferent (I, H) ((cap0, (#1 dir0, tubes0)), (ty, NONE, K.top))
         >:? goalTy0 >:? goalTy
        #> (I, H, trivial)
      end

    fun EqCapL alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.EqCapL"
        val (I, H) >> CJ.EQ ((hcom, other), (ty, l, k)) = jdg
        val k = K.meet (k, K.HCOM)
        (* these operations could be expensive *)
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out hcom
        val () = Assert.paramEq "HCom.EqCapL source and target of direction" (r, r')

        (* equations *)
        val _ = Assert.tautologicalEquations "HCom.EqCapL tautology checking" (List.map #1 tubes)

        (* type *)
        val goalTy0 = makeEqTypeIfDifferent (I, H) ((ty0, ty), l, k)

        (* eq *)
        val goalEq = makeEq (I, H) ((cap, other), (ty, l, k))

        val w = alpha 0
      in
        |>: goalEq
         >:+ ComKit.genInterTubeGoals (I, H) w ((tubes, tubes), (ty, l, k))
         >:+ ComKit.genCapTubeGoalsIfDifferent (I, H) ((cap, (r, tubes)), (ty, NONE, K.top))
         >:? goalTy0
        #> (I, H, trivial)
      end

    (* Search for the first satisfied equation in an hcom. *)
    fun EqTubeL alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.EqTubeL"
        val (I, H) >> CJ.EQ ((hcom, other), (ty, l, k)) = jdg
        val k = K.meet (k, K.HCOM)
        (* these operations could be expensive *)
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out hcom

        (* equations. they must be tautological because one of them is true. *)
        val (_, (u, tube)) = Option.valOf (List.find (fn (eq, _) => P.eq Sym.eq eq) tubes)

        (* type *)
        (* the cap-tube adjacency premise guarantees that [ty] is a type
         * because one of the equations is true, and thus alpha-equivalence
         * is sufficient. *)
        val goalTy0 = makeEqTypeIfDifferent (I, H) ((ty0, ty), l, k)

        (* cap *)
        (* the cap-tube adjacency premise guarantees that [cap] is in [ty],
         * and thus there is nothing to prove! Yay! *)

        (* eq *)
        (* the tube-tube adjacency premise guarantees that this particular tube
         * is unconditionally in [ty], and thus alpha-equivalence is sufficient. *)
        val goalEq = makeEqIfDifferent (I, H) ((substSymbol (r', u) tube, other), (ty, l, k))

        val w = alpha 0
      in
        |>:? goalEq
         >:+ ComKit.genInterTubeGoals (I, H) w ((tubes, tubes), (ty, l, k))
         >:+ ComKit.genCapTubeGoalsIfDifferent (I, H) ((cap, (r, tubes)), (ty, NONE, K.top))
         >:? goalTy0
        #> (I, H, trivial)
      end
  end
end
