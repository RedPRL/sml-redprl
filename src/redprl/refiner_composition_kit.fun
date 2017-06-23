functor RefinerCompositionKit (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = abt CJ.jdg
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
       all cases. We need to generalize the old handling to
       welcome new hcom operators. (It is true that we still
       only need to handle context restrictions with at most two
       equations, but it seems easier to just handle all cases.)

       Such automation is possible because the rules are "syntax
       directed" on the restriction being performed.
     *)

    (* Restrict a judgement (as the goal) by a list of equations.
     * Returns NONE if the resulting judgement is vacuously true.
     *)
    val restrict : abt jdg -> (param * param) list -> abt jdg option
  end
  =
  struct
    (* A helper function which does substitution in a parameter. *)
    fun substSymInParam (r, v) = P.bind (fn u => if Sym.eq (u, v) then r else P.ret u)

    fun restrict jdg [] = SOME jdg
      | restrict jdg ((P.APP d1, P.APP d2) :: eqs) =
          (* The following line is correct because we only have constants
           * (DIM0 and DIM1). If in the future we want to have connections
           * or other stuff, then a real unification algorithm might be needed.
           *)
          if P.Sig.eq (fn _ => true) (d1, d2) then restrict jdg eqs else NONE
      | restrict jdg ((r1 as P.VAR v1, r2) :: eqs) =
          if P.eq Sym.eq (r1, r2) then restrict jdg eqs else substAndRestrict (r2, v1) jdg eqs
      | restrict jdg ((r1, r2 as P.VAR v2) :: eqs) =
          substAndRestrict (r1, v2) jdg eqs

    and substAndRestrict rv jdg eqs = restrict
          (Seq.map (substSymbol rv) jdg)
          (List.map (fn (r, r') => (substSymInParam rv r, substSymInParam rv r')) eqs)
  end

  (* code shared by Com, HCom and FCom. *)
  structure ComKit =
  struct
    (* todo: optimizing the restriction process even further. *)
    (* todo: pre-restrict r=0, r=1, 0=r and 1=r, and open-reduce everything first. *)
    (* todo: do alpha-renaming only once. *)
    (* todo: try to reduce substitution. *)

    (* Produce the list of goals requiring that tube aspects agree with each other.
         forall i <= j.
           N_i = P_j in A [Psi, y | r_i = r_i', r_j = r_j']
     *)
    fun genInterTubeGoals (I, H) w ty tubes0 tubes1 =
      let
        fun interTube (eq0, (u, tube0)) (eq1, (v, tube1)) =
          let
            val tube0 = substSymbol (P.ret w, u) tube0
            val tube1 = substSymbol (P.ret w, v) tube1
            val J = (I @ [(w,P.DIM)], H) >> CJ.EQ ((tube0, tube1), ty)
          in
            Option.map makeGoal' (Restriction.restrict J [eq0, eq1])
          end
        fun goTubePairs [] [] = []
          | goTubePairs (t0 :: ts0) (t1 :: ts1) =
              List.mapPartial (interTube t0) (t1 :: ts1) :: goTubePairs ts0 ts1
          | goTubePairs _ _ = raise
              E.error [Fpp.text "interTubeGoals: the tubes are of different lengths"]
      in
        List.concat (goTubePairs tubes0 tubes1)
      end

    (* Produce the list of goals requiring that tube aspects agree with the cap.
         forall i.
           N_i<r/y> = M in A [Psi | r_i = r_i']
     *)
    fun genTubeCapGoals (I, H) ty r cap tubes =
      let
        fun tubeCap (eq, (u, tube)) =
          let
            val J = (I, H) >> CJ.EQ ((substSymbol (r, u) tube, cap), ty)
          in
            Option.map makeGoal' (Restriction.restrict J [eq])
          end
      in
        List.mapPartial tubeCap tubes
      end

    (* Note that this does not check whether the 'ty' is a base type.
     * It's caller's responsibility to check whether the type 'ty'
     * recognizes FCOM as values. *)
    fun EqFComDelegator alpha (I, H) args0 args1 ty =
      let
        val {dir=(r0, r'0), cap=cap0, tubes=tubes0} = args0
        val {dir=(r1, r'1), cap=cap1, tubes=tubes1} = args1
        val () = Assert.paramEq "EqFComDelegator source of direction" (r0, r1)
        val () = Assert.paramEq "EqFComDelegator target of direction" (r'0, r'1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = ListPair.mapEq (Assert.equationEq "EqFComDelegator equations") (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "EqFComDelegator tautology checking" eqs0

        val goalCap = makeGoal' @@ (I, H) >> CJ.EQ ((cap0, cap1), ty)

        val w = alpha 0
      in
        T.empty
          >: goalCap
          >:+ genInterTubeGoals (I, H) w ty tubes0 tubes1
          >:+ genTubeCapGoals (I, H) ty r0 cap0 tubes0
        #> (I, H, trivial)
      end
  end

  structure HCom =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.HCOM {dir=(r0, r'0), ty=ty0, cap=cap0, tubes=tubes0} = Syn.out lhs
        val Syn.HCOM {dir=(r1, r'1), ty=ty1, cap=cap1, tubes=tubes1} = Syn.out rhs
        val () = Assert.paramEq "HCom.Eq source of direction" (r0, r1)
        val () = Assert.paramEq "HCom.Eq target of direction" (r'0, r'1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = ListPair.mapEq (Assert.equationEq "HCom.Eq equations") (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "HCom.Eq tautology checking" eqs0

        (* type *)
        val goalTy0 = makeEqTypeIfDifferent (I, H) (ty0, ty)
        val goalTy01 = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (ty0, ty1)

        (* cap *)
        val goalCap01 = makeGoal' @@ (I, H) >> CJ.EQ ((cap0, cap1), ty)

        val w = alpha 0
      in
        T.empty
          >:? goalTy0 >: goalTy01 >: goalCap01
          >:+ ComKit.genInterTubeGoals (I, H) w ty0 tubes0 tubes1
          >:+ ComKit.genTubeCapGoals (I, H) ty r0 cap0 tubes0
        #> (I, H, trivial)
      end

    fun CapEqL alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.CapEq"
        val (I, H) >> CJ.EQ ((hcom, other), ty) = jdg
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out hcom
        val () = Assert.paramEq "HCom.CapEq source and target of direction" (r, r')
  
        (* type *)
        val goalTy0 = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (ty0, ty)

        (* eq *)
        val goalEq = makeGoal' @@ (I, H) >> CJ.EQ ((cap, other), ty)
  
        val w = alpha 0
      in
        T.empty
          >: goalTy0 >: goalEq
          >:+ ComKit.genInterTubeGoals (I, H) w ty tubes tubes
          >:+ ComKit.genTubeCapGoals (I, H) ty r cap tubes
        #> (I, H, trivial)
      end

    val CapEqR = catJdgFlipWrapper CapEqL

    (* Search for the first satisfied equation in an hcom. *)
    fun TubeEqL alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.TubeEq"
        val (I, H) >> CJ.EQ ((hcom, other), ty) = jdg
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out hcom
        val (eq, (u, tube)) = Option.valOf (List.find (fn (eq, _) => P.eq Sym.eq eq) tubes)

        (* type *)
        val goalTy0 = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (ty0, ty)

        (* cap *)
        val goalCap = makeGoal' @@ (I, H) >> CJ.MEM (cap, ty)

        (* eq *)
        val goalEq = makeGoal' @@ (I, H) >> CJ.EQ ((substSymbol (r', u) tube, other), ty)
  
        val w = alpha 0
      in
        T.empty
          >: goalTy0 >: goalCap >: goalEq
          >:+ ComKit.genInterTubeGoals (I, H) w ty tubes tubes
          >:+ ComKit.genTubeCapGoals (I, H) ty r cap tubes
        #> (I, H, trivial)
      end

    val TubeEqR = catJdgFlipWrapper TubeEqL

    (* Try all the hcom rules.
     * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
    val AutoEqLR = CapEqL orelse_ CapEqR orelse_ TubeEqL orelse_ TubeEqR orelse_ Eq
    val AutoEqL = CapEqL orelse_ TubeEqL orelse_ Eq
    val AutoEqR = CapEqR orelse_ TubeEqR orelse_ Eq
  end

  structure Com =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Com.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COM {dir=(r0, r'0), ty=(u0,ty0), cap=cap0, tubes=tubes0} = Syn.out lhs
        val Syn.COM {dir=(r1, r'1), ty=(u1,ty1), cap=cap1, tubes=tubes1} = Syn.out rhs
        val () = Assert.paramEq "Com.Eq source of direction" (r0, r1)
        val () = Assert.paramEq "Com.Eq target of direction" (r'0, r'1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = ListPair.mapEq (Assert.equationEq "Com.Eq equations") (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "Com.Eq tautology checking" eqs0

        val w = alpha 0

        (* type *)
        val goalTy0 = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (substSymbol (r'0, u0) ty0, ty)
        val ty0w = substSymbol (P.ret w, u0) ty0
        val ty1w = substSymbol (P.ret w, u1) ty1
        val goalTy01 = makeGoal' @@ (I @ [(w,P.DIM)], H) >> CJ.EQ_TYPE (ty0w, ty1w)

        (* cap *)
        val ty00 = substSymbol (r0, u0) ty0
        val goalCap = makeGoal' @@ (I, H) >> CJ.EQ ((cap0, cap1), ty00)
      in
        T.empty
          >: goalTy0 >: goalTy01 >: goalCap
          >:+ ComKit.genInterTubeGoals (I, H) w ty0w tubes0 tubes1
          >:+ ComKit.genTubeCapGoals (I, H) ty00 r0 cap0 tubes0
        #> (I, H, trivial)
      end

    fun CapEqL alpha jdg =
      let
        val _ = RedPrlLog.trace "Com.CapEq"
        val (I, H) >> CJ.EQ ((com, other), ty) = jdg
        val Syn.COM {dir=(r, r'), ty=(u0,ty0), cap, tubes} = Syn.out com
        val () = Assert.paramEq "Com.CapEq source and target of direction" (r, r')

        (* type *)
        val goalTy0 = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (substSymbol (r', u0) ty0, ty)

        (* eq *)
        val goalEq = makeGoal' @@ (I, H) >> CJ.EQ ((cap, other), ty)

        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u0) ty0
        val ty00 = substSymbol (r, u0) ty0
      in
        T.empty
          >: goalTy0 >: goalEq
          >:+ ComKit.genInterTubeGoals (I, H) w ty0w tubes tubes
          >:+ ComKit.genTubeCapGoals (I, H) ty00 r cap tubes
        #> (I, H, trivial)
      end

    val CapEqR = catJdgFlipWrapper CapEqL

    (* Search for the first satisfied equation in an hcom. *)
    fun TubeEqL alpha jdg =
      let
        val _ = RedPrlLog.trace "Com.TubeEq"
        val (I, H) >> CJ.EQ ((com, other), ty) = jdg
        val Syn.COM {dir=(r, r'), ty=(u0,ty0), cap, tubes} = Syn.out com
        val (eq, (u, tube)) = Option.valOf (List.find (fn (eq, _) => P.eq Sym.eq eq) tubes)

        (* type *)
        val goalTy0 = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (substSymbol (r', u0) ty0, ty)

        (* cap *)
        val ty00 = substSymbol (r, u0) ty0
        val goalCap = makeGoal' @@ (I, H) >> CJ.MEM (cap, ty00)

        (* eq *)
        val goalEq = makeGoal' @@ (I, H) >> CJ.EQ ((substSymbol (r', u) tube, other), ty)

        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u0) ty0
      in
        T.empty
          >: goalTy0 >: goalCap >: goalEq
          >:+ ComKit.genInterTubeGoals (I, H) w ty0w tubes tubes
          >:+ ComKit.genTubeCapGoals (I, H) ty00 r cap tubes
        #> (I, H, trivial)
      end

    val TubeEqR = catJdgFlipWrapper TubeEqL

    (* Try all the hcom rules.
     * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
    val AutoEqLR = CapEqL orelse_ CapEqR orelse_ TubeEqL orelse_ TubeEqR orelse_ Eq
    val AutoEqL = CapEqL orelse_ TubeEqL orelse_ Eq
    val AutoEqR = CapEqR orelse_ TubeEqR orelse_ Eq
  end
end
