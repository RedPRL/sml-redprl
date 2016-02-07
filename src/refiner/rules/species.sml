structure SpeciesRules : SPECIES_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ >> $ $# \

  fun destSpecies m =
    case out m of
         CTT (SPECIES tau) $ [_ \ a, (_, [x]) \ b] => (tau, a, x, b)
       | _ =>
           raise Fail
             @@ "Expected Species but got "
              ^ DebugShowAbt.toString m

  fun makeEq mctx (m,n,a) =
    check
      mctx
      (CTT (EQ (sort m)) $ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a],
       EXP)

  fun makeMember mctx (m,a) =
    check
      mctx
      (CTT (MEMBER (sort m)) $ [([],[]) \ m, ([],[]) \ a],
       EXP)

  fun makeSquash mctx tau a =
    check
      mctx
      (CTT (SQUASH tau) $ [([],[]) \ a],
       EXP)

  fun makeEqSequent H args =
    H >> (makeEq (#metactx H) args, TRIV)

  fun makeMemberSequent H args =
    H >> (makeMember (#metactx H) args, TRIV)

  fun makeLevelSequent (H : Sequent.context) =
    let
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.empty}
    in
      H' >> (check' (CTT (BASE LVL) $ [], EXP), LVL)
    end


  fun TypeEq alpha (H >> (P, _)) =
    let
      val (tau,s1,s2,univ) = destEq P
      val (_, a1, x1, b1) = destSpecies s1
      val (_, a2, x2, b2) = destSpecies s2
      val _ = destUniv univ

      val goal1 =
        (newMeta "",
         makeEqSequent H (a1,a2,univ))

      val x = alpha 0
      val xtm = check' (`x, tau)
      val b1x = subst (xtm, x1) b1
      val b2x = subst (xtm, x2) b2

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) (x, (a1, tau))}

      val goal2 =
        (newMeta "",
         makeEqSequent H' (b1x, b2x, univ))

      val psi =
        T.snoc (T.snoc T.empty goal1) goal2
    in
      (psi, fn rho =>
        abtToAbs (check' (CTT AX $ [], TRIV)))
    end

  fun MemberEq alpha (H >> (P, _)) =
    let
      val (_, m1, m2, sp) = destEq P
      val (tau, a, x, b) = destSpecies sp
      val tyGoal =
        (newMeta "",
         makeEqSequent H (m1, m2, a))

      val squashGoal =
        (newMeta "",
         H >> (makeSquash (#metactx H) tau a, TRIV))

      val z = alpha 0
      val bz = subst (check' (`z, tau), x) b

      val lvlGoal = (newMeta "", makeLevelSequent H)
      val H' =
        {metactx = MetaCtx.insert (#metactx H) (#1 lvlGoal) (([],[]), LVL),
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) (z, (a, tau))}

      val lvlHole =
        check
          (#metactx H')
          (#1 lvlGoal $# ([], []),
           LVL)
      val univ =
        check
          (#metactx H')
          (CTT (UNIV tau) $ [([],[]) \ lvlHole],
           EXP)

      val tyfunGoal =
        (newMeta "",
         makeMemberSequent H' (bz, univ))

      fun @> (t,g) = T.snoc t g
      infix @>

      val psi = T.empty @> tyGoal @> squashGoal @> lvlGoal @> tyfunGoal
    in
      (psi, fn rho =>
        abtToAbs @@ check' (CTT AX $ [], TRIV))
    end
end
