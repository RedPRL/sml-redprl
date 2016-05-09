structure EnsembleRules : ENSEMBLE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix 0 @@
  infix 1 $ $$ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun destEnsemble m =
    case out m of
         CTT (ENSEMBLE (tau1, tau2)) $ [_ \ a, (_, [x]) \ b] => (tau1, tau2, a, x, b)
       | _ =>
           raise Fail
             @@ "Expected Ensemble but got "
              ^ DebugShowAbt.toString m

  fun IsType alpha (goal as (H >> TYPE (ty, sigma))) =
    let
      val (sigma', tau, a, x, bx) = destEnsemble ty
      val _ = if Sort.eq (sigma, sigma') then () else raise Fail "Sort mismatch"

      val (goalA, holeA, H') =
        makeGoal @@
          H >> TYPE (a, sigma)

      val Hx = updateHyps (fn xs => Ctx.snoc xs x (a, sigma)) H'

      val (goalB, _, H') =
        makeGoal @@
          Hx >> TYPE (bx, tau)

      val psi = T.empty @> goalA @> goalB
    in
      (psi, fn rho =>
        let
          val l1 = T.lookup rho (#1 goalA) // ([],[])
          val l2 = T.lookup rho (#1 goalB) // ([],[])
          (* TODO: do we need to ensure that x is not free in l2? *)
        in
          abtToAbs @@ LVL_OP LSUP $$ [([],[]) \ l1, ([],[]) \ l2]
        end)
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (goal as (H >> EQ_MEM (s1, s2, univ))) =
    let
      val (sigma1, tau1, a1, x1, b1) = destEnsemble s1
      val (sigma1, tau1, a2, x2, b2) = destEnsemble s2
    in
      QuantifierKit.TypeEq (CTT (ENSEMBLE (sigma1, tau1))) alpha goal
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (m1, m2, ensemble)) =
    let
      val (tau1, tau2, a, x, b) = destEnsemble ensemble

      val (tyGoal, _, H) =
        makeGoal @@
          makeEqSequent H (m1, m2, a)

      val bm = subst (m1, x) b
      val (squashGoal, _, H) =
        makeGoal @@
          H >> TRUE (makeSquash tau2 bm, EXP)

      val z = alpha 0
      val bz = subst (check (`z, tau1), x) b

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, tau1)) H

      val (tyfunGoal, _, _) =
        makeGoal @@
          [(z,tau1)] |> H' >> TYPE (bz, tau2)

      val psi = T.empty @> tyGoal @> squashGoal @> tyfunGoal
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  fun Intro alpha (H >> TRUE (P, _)) =
    let
      val (tau1, tau2, a, x, b) = destEnsemble P

      val (mainGoal, mainHole, H) =
        makeGoal @@
          H >> TRUE (a, tau1)

      val pred = subst (mainHole [] [], x) b
      val (predGoal, _, H) =
        makeGoal @@
          H >> TRUE (makeSquash tau2 pred, EXP)

      val z = alpha 0
      val bz = subst (check (`z, tau1), x) b

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, tau1)) H

      val (tyfunGoal, _, _) =
        makeGoal @@
          [(z,tau1)] |> H' >> TYPE (bz, tau2)

      val psi = T.empty @> mainGoal @> predGoal @> tyfunGoal
    in
      (psi, fn rho =>
        T.lookup rho (#1 mainGoal))
    end
    | Intro _ _ = raise Match

  fun Elim i alpha (H >> TRUE (P, tau)) =
    let
      val (ensemble, _) = Ctx.lookup (getHyps H) i
      val (tau1, tau2, a, x, bx) = destEnsemble ensemble
      val (z1, z2) = (alpha 0, alpha 1)
      val z1tm = check (`z1, tau1)
      val bz1 = makeSquash tau2 (subst (z1tm, x) bx)
      val hyps =
        Ctx.interposeAfter
          (getHyps H)
          (i, Ctx.snoc (Ctx.snoc Ctx.empty z1 (a, tau1)) z2 (bz1, tau2))

      val hyps' =
        Ctx.modifyAfter i
          (fn (p,tau) => (subst (z1tm, i) p, tau))
          hyps

      val H' = updateHyps (fn _ => hyps') H
      val P' = subst (z1tm, i) P

      val (goal, _, _) =
        makeGoal @@
          [(z1, tau1), (z2, tau2)] |> H' >> TRUE (P', tau)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        let
          val itm = check (`i, tau1)
        in
          abtToAbs @@
            T.lookup rho (#1 goal) // ([], [itm, makeAx])
        end)
    end
    | Elim _ _ _ = raise Match
end
