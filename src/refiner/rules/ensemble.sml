structure EnsembleRules : ENSEMBLE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ >> $ $# \ @>

  fun destEnsemble m =
    case out m of
         CTT (ENSEMBLE (tau1, tau2)) $ [_ \ a, (_, [x]) \ b] => (tau1, tau2, a, x, b)
       | _ =>
           raise Fail
             @@ "Expected Ensemble but got "
              ^ DebugShowAbt.toString m

  fun TypeEq alpha (H >> TRUE (P, _)) =
    let
      val (tau,s1,s2,univ) = destEq P
      val (_, _, a1, x1, b1) = destEnsemble s1
      val (_, _, a2, x2, b2) = destEnsemble s2
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
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> TRUE (P, _)) =
    let
      val (_, m1, m2, ensemble) = destEq P
      val (tau1, tau2, a, x, b) = destEnsemble ensemble
      val tyGoal =
        (newMeta "",
         makeEqSequent H (m1, m2, a))

      val bm = subst (m1, x) b
      val squashGoal =
        (newMeta "",
         H >> TRUE (makeSquash (#metactx H) tau2 bm, EXP))

      val z = alpha 0
      val bz = subst (check' (`z, tau1), x) b

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) (z, (a, tau1))}

      val tyfunGoal =
        (newMeta "",
         H' >> TYPE (bz, tau2))

      val psi = T.empty @> tyGoal @> squashGoal @> tyfunGoal
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  fun Intro alpha (H >> TRUE (P, _)) =
    let
      val (tau1, tau2, a, x, b) = destEnsemble P

      val mainGoal =
        (newMeta "",
         H >> TRUE (a, tau1))

      val H' =
        {metactx = MetaCtx.insert (#metactx H) (#1 mainGoal) (([],[]), tau1),
         symctx = #symctx H,
         hypctx = #hypctx H}

      val mainHole = check (#metactx H') (#1 mainGoal $# ([],[]), tau1)
      val pred = subst (mainHole, x) b
      val predGoal =
        (newMeta "",
         H >> TRUE (makeSquash (#metactx H) tau2 pred, EXP))

      val z = alpha 0
      val bz = subst (check' (`z, tau1), x) b

      val H'' =
        {metactx = #metactx H',
         symctx = #symctx H',
         hypctx = Ctx.snoc (#hypctx H') (z, (a, tau1))}

      val tyfunGoal =
        (newMeta "",
         H'' >> TYPE (bz, tau2))

      val psi = T.empty @> mainGoal @> predGoal @> tyfunGoal
    in
      (psi, fn rho =>
        T.lookup rho (#1 mainGoal))
    end
    | Intro _ _ = raise Match

  fun Elim i alpha (H >> TRUE (P, tau)) =
    let
      val (ensemble, _) = Ctx.lookup (#hypctx H) i
      val (tau1, tau2, a, x, bx) = destEnsemble ensemble
      val (z1, z2) = (alpha 0, alpha 1)
      val z1tm = check' (`z1, tau1)
      val bz1 = makeSquash (#metactx H) tau2 (subst (z1tm, x) bx)
      val hyps =
        Ctx.interposeAfter
          (#hypctx H)
          (i, Ctx.snoc (Ctx.snoc Ctx.empty (z1, (a, tau1))) (z2, (bz1, tau2)))
      val hyps' =
        Ctx.mapAfter
          hyps
          (i, fn (p,tau) => (subst (z1tm, i) p, tau))

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = hyps'}

      val P' = subst (z1tm, i) P

      val goal =
        (newMeta "",
         H' >> TRUE (P', tau))

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        let
          val itm = check' (`i, tau1)
          val varEnv = VarCtx.insert (VarCtx.insert VarCtx.empty z1 itm) z2 makeAx
        in
          mapAbs
            (substEnv varEnv)
            (T.lookup rho (#1 goal))
        end)
    end
    | Elim _ _ _ = raise Match
end
