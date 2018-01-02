functor RefinerCompositionKit (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  structure Syn = SyntaxView
  structure Abt = RedPrlAbt
  open Abt Kit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = AJ.jdg
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
    val restrict : (abt * abt) list -> (abt -> abt) option
  end
  =
  struct
    (* precondition: all term in equations are of sort `DIM` *)
    fun restrict' [] (f : abt -> abt) = SOME f
      | restrict' ((r1, r2) :: eqs) (f : abt -> abt) = 
          (case (Syn.out r1, Syn.out r2) of
              (Syn.DIM0, Syn.DIM0) => restrict' eqs f
            | (Syn.DIM0, Syn.DIM1) => NONE
            | (Syn.DIM1, Syn.DIM1) => restrict' eqs f
            | (Syn.DIM1, Syn.DIM0) => NONE
            | (Syn.VAR (v1, _), _) => if Abt.eq (r1, r2) then restrict' eqs f else substAndRestrict' (r2, v1) eqs f
            | (Syn.META (v1, _), _) => if Abt.eq (r1, r2) then restrict' eqs f else substMetaAndRestrict' (r2, v1) eqs f
            | (_, Syn.VAR (v2, _)) => substAndRestrict' (r1, v2) eqs f
            | (_, Syn.META (v2, _)) => substMetaAndRestrict' (r1, v2) eqs f)

    and substMetaAndRestrict' (r, v) eqs f =
        let
          val abs = abtToAbs r
        in
          restrict'
            (List.map (fn (r1, r2) => (substMetavar (abs, v) r1, substMetavar (abs, v) r2)) eqs)
            (substMetavar (abs, v) o f)
        end

    and substAndRestrict' rv eqs f =
          restrict'
            (List.map (fn (r, r') => (substVar rv r, substVar rv r')) eqs)
            (substVar rv o f)

    fun restrict eqs = restrict' eqs (fn x => x)
  end
  (* adding some helper functions *)
  structure Restriction =
  struct
    open Restriction

    fun makeEq tr eqs H ((m, n), ty) =
      Option.map
        (fn f => makeEqWith tr f H ((m, n), ty))
        (restrict eqs)

    fun makeEqIfDifferent tr eqs H ((m, n), ty) =
      Option.mapPartial
        (fn f =>
          if Abt.eq (f m, f n) then NONE
          else SOME @@ makeEqWith tr f H ((m, n), ty))
        (restrict eqs)

    fun makeMem tr eqs H (m, ty) =
      makeEq tr eqs H ((m, m), ty)

    fun makeEqType tr eqs H ((a, b), k) =
      Option.map
        (fn f => makeEqTypeWith tr f H ((a, b), k))
        (restrict eqs)

    fun makeEqTypeIfDifferent tr eqs H ((a, b), k) =
      Option.mapPartial
        (fn f =>
          if Abt.eq (f a, f b) then NONE
          else SOME @@ makeEqTypeWith tr f H ((a, b), k))
        (restrict eqs)

    fun makeTrue tr eqs default H a =
      case restrict eqs of
        NONE => (NONE, default)
      | SOME f =>
          let
            val (goal, hole) = makeTrueWith tr f H a
          in
            (SOME goal, hole)
          end

    structure View =
    struct
      fun makeAsEqType tr eqs H ((a, b), l, k) =
        Option.mapPartial
          (fn f => SOME @@ View.makeAsEqTypeWith tr f H ((a, b), l, k))
          (restrict eqs)

      fun makeAsEqTypeIfDifferent tr eqs H ((a, b), l, k) =
        Option.mapPartial
          (fn f =>
            if Abt.eq (f a, f b) then NONE
            else SOME @@ View.makeAsEqTypeWith tr f H ((a, b), l, k))
          (restrict eqs)
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
    fun alphaRenameTubes w = List.map (fn (eq, (u, tube)) => (eq, substVar (VarKit.toDim w, u) tube))
    fun enumInterExceptDiag f =
      let
        fun enum ([], []) = []
          | enum ((t0 :: ts0), (_ :: ts1)) = List.mapPartial (fn t1 => f (t0, t1)) ts1 :: enum (ts0, ts1)
          | enum _ = E.raiseError @@ E.IMPOSSIBLE @@ Fpp.text "enumInterExceptDiag: inputs are of different lengths"
      in
        List.concat o enum
      end

    local
      (* TODO: why do these have tick marks after them? - JMS *)
      fun genTubeGoals' tr (H : AJ.jdg Hyps.telescope) ((tubes0, tubes1), ty) =
        ListPairUtil.mapPartialEq
          (fn ((eq, t0), (_, t1)) => Restriction.makeEq tr [eq] H ((t0, t1), ty))
          (tubes0, tubes1)

      fun genInterTubeGoalsExceptDiag' tr (H : AJ.jdg Hyps.telescope) ((tubes0, tubes1), ty) =
        enumInterExceptDiag
          (fn ((eq0, t0), (eq1, t1)) => Restriction.makeEqIfDifferent tr [eq0, eq1] H ((t0, t1), ty))
          (tubes0, tubes1)
    in
      fun genInterTubeGoals tr (H : AJ.jdg Hyps.telescope) w ((tubes0, tubes1), ty) =
        let
          val tubes0 = alphaRenameTubes w tubes0
          val tubes1 = alphaRenameTubes w tubes1

          val goalsOnDiag = genTubeGoals' tr (H @> (w, AJ.TERM O.DIM)) ((tubes0, tubes1), ty)
          val goalsNotOnDiag = genInterTubeGoalsExceptDiag' tr (H @> (w, AJ.TERM O.DIM)) ((tubes0, tubes1), ty)
        in
          goalsOnDiag @ goalsNotOnDiag
        end
    end

    (* Produce the list of goals requiring that tube aspects agree with the cap.
         forall i.
           M = N_i<r/y> in A [Psi | r_i = r_i']
     *)
    fun genCapTubeGoalsIfDifferent tr H ((cap, (r, tubes)), ty) =
      List.mapPartial
        (fn (eq, (u, tube)) =>
          Restriction.makeEqIfDifferent tr [eq] H ((cap, substVar (r, u) tube), ty))
        tubes

    (* Note that this does not check whether the 'ty' is a base type.
     * It's caller's responsibility to check whether the type 'ty'
     * recognizes FCOM as values. *)
    fun genEqFComGoals tr H w (args0, args1) ty =
      let
        val {dir=dir0, cap=cap0, tubes=tubes0 : abt Syn.tube list} = args0
        val {dir=dir1, cap=cap1, tubes=tubes1 : abt Syn.tube list} = args1
        val () = Assert.dirEq "genFComGoals" (dir0, dir1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = Assert.equationsEq "genFComGoals equations" (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "genFComGoals tautology checking" eqs0

        val goalCap = makeEq tr H ((cap0, cap1), ty)
      in
           goalCap
        :: genInterTubeGoals tr H w ((tubes0, tubes1), ty)
         @ genCapTubeGoalsIfDifferent tr H ((cap0, (#1 dir0, tubes0)), ty)
      end
  end

  structure HCom =
  struct
    fun Eq alpha jdg =
      let
        val tr = ["HCom.Eq"]

        val H >> ajdg = jdg
        val ((lhs, rhs), ty) = View.matchAsEq ajdg
        val k = K.HCOM
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
        val goalTy0 = makeType tr H (ty0, k)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (ty0, ty) (* (ty0, k) is proved *)

        (* cap *)
        val goalCap = makeEq tr H ((cap0, cap1), ty0)

        val w = alpha 0
      in
        |>: goalCap
         >:+ ComKit.genInterTubeGoals tr H w ((tubes0, tubes1), ty0)
         >:+ ComKit.genCapTubeGoalsIfDifferent tr H ((cap0, (#1 dir0, tubes0)), ty0)
         >: goalTy0 >:? goalTy
        #> (H, axiom)
      end

    fun EqCapL alpha jdg =
      let
        val tr = ["HCom.EqCapL"]

        val H >> ajdg = jdg
        val ((hcom, other), ty) = View.matchAsEq ajdg
        val k = K.HCOM
        (* these operations could be expensive *)
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out hcom
        val () = Assert.alphaEq' "HCom.EqCapL source and target of direction" (r, r')

        (* equations *)
        val _ = Assert.tautologicalEquations "HCom.EqCapL tautology checking" (List.map #1 tubes)

        (* type *)
        val goalTy0 = makeType tr H (ty0, k)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (ty0, ty) (* (ty0, k) is proved *)

        (* eq *)
        val goalEq = View.makeAsEq tr H ((cap, other), ty)

        val w = alpha 0
      in
        |>: goalEq
         >:+ ComKit.genInterTubeGoals tr H w ((tubes, tubes), ty0)
         >:+ ComKit.genCapTubeGoalsIfDifferent tr H ((cap, (r, tubes)), ty0)
         >: goalTy0 >:? goalTy
        #> (H, axiom)
      end

    (* Search for the first satisfied equation in an hcom. *)
    fun EqTubeL alpha jdg =
      let
        val tr = ["HCom.EqTubeL"]

        val H >> ajdg = jdg
        val ((hcom, other), ty) = View.matchAsEq ajdg
        val k = K.HCOM
        (* these operations could be expensive *)
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out hcom

        (* equations. they must be tautological because one of them is true. *)
        val (_, (u, tube)) = Option.valOf (List.find (fn (eq, _) => Abt.eq eq) tubes)

        (* type *)
        val goalTy0 = makeType tr H (ty0, k)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (ty0, ty) (* (ty0, k) is proved *)

        (* cap *)
        (* the cap-tube adjacency premise guarantees that [cap] is in [ty0],
         * and thus there is nothing to prove! Yay! *)

        (* eq *)
        (* the tube-tube adjacency premise guarantees that this particular tube
         * is unconditionally in [ty], and thus alpha-equivalence is sufficient. *)
        val goalEq = makeEqIfDifferent tr H ((substVar (r', u) tube, other), ty0)

        val w = alpha 0
      in
        |>:? goalEq
         >:+ ComKit.genInterTubeGoals tr H w ((tubes, tubes), ty0)
         >:+ ComKit.genCapTubeGoalsIfDifferent tr H ((cap, (r, tubes)), ty0)
         >: goalTy0 >:? goalTy
        #> (H, axiom)
      end
  end
end
