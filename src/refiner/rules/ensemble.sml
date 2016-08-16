structure EnsembleRules : ENSEMBLE_RULES =
struct
  open RefinerKit
  infixr 0 @@
  infix 1 $ $$ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun destEnsemble m =
    case Syn.out m of
       Syn.ENSEMBLE (_, _, a, x, bx) => (a, x, bx)
     | _ => raise Match

  fun IsType alpha (goal as (H >> TYPE (ty, sigma))) =
    let
      val Syn.ENSEMBLE (sigma', tau, a, x, bx) = Syn.out ty
      val _ = if sigma = sigma' then () else raise Fail "Sort mismatch"

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
          abtToAbs @@ Syn.into @@ Syn.LSUP (l1, l2)
        end)
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (goal as (H >> EQ_MEM (s1, s2, univ))) =
    let
      (* TODO: What are the following lines doing? Delete these once sober *)
      val Syn.ENSEMBLE (sigma1, tau1, a1, x1, b1) = Syn.out s1
      val Syn.ENSEMBLE (sigma1, tau1, a2, x2, b2) = Syn.out s2
    in
      QuantifierKit.TypeEq destEnsemble alpha goal
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (m1, m2, ensemble)) =
    let
      val Syn.ENSEMBLE (tau1, tau2, a, x, b) = Syn.out ensemble

      val (tyGoal, _, H) =
        makeGoal @@
          makeEqSequent H (m1, m2, a)

      val bm = subst (m1, x) b
      val (squashGoal, _, H) =
        makeGoal @@
          H >> TRUE (Syn.into (Syn.SQUASH (tau2, bm)), SortData.EXP)

      val z = alpha 0
      val bz = subst (check (`z, RS.EXP tau1), x) b

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, tau1)) H

      val (tyfunGoal, _, _) =
        makeGoal @@
          ([], [(z,tau1)]) |> H' >> TYPE (bz, tau2)

      val psi = T.empty @> tyGoal @> squashGoal @> tyfunGoal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  fun Intro alpha (H >> TRUE (P, _)) =
    let
      val Syn.ENSEMBLE (tau1, tau2, a, x, b) = Syn.out P

      val (mainGoal, mainHole, H) =
        makeGoal @@
          H >> TRUE (a, tau1)

      val pred = subst (mainHole [] [], x) b

      val (predGoal, _, H) =
        makeGoal @@
          H >> TRUE (Syn.into (Syn.SQUASH (tau2, pred)), SortData.EXP)

      val z = alpha 0
      val bz = subst (check (`z, RS.EXP tau1), x) b

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, tau1)) H

      val (tyfunGoal, _, _) =
        makeGoal @@
          ([], [(z,tau1)]) |> H' >> TYPE (bz, tau2)

      val psi = T.empty @> mainGoal @> predGoal @> tyfunGoal
    in
      (psi, fn rho =>
        T.lookup rho (#1 mainGoal))
    end
    | Intro _ _ = raise Match

  fun Elim i alpha (H >> TRUE (P, tau)) =
    let
      val (ensemble, _) = Ctx.lookup (getHyps H) i
      val Syn.ENSEMBLE (tau1, tau2, a, x, bx) = Syn.out ensemble
      val (z1, z2) = (alpha 0, alpha 1)
      val z1tm = check (`z1, RS.EXP tau1)
      val bz1 = Syn.into @@ Syn.SQUASH (tau2, (subst (z1tm, x) bx))
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
          ([], [(z1, tau1), (z2, tau2)]) |> H' >> TRUE (P', tau)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        let
          val itm = check (`i, RS.EXP tau1)
        in
          abtToAbs @@
            T.lookup rho (#1 goal) // ([], [itm, Syn.into Syn.AX])
        end)
    end
    | Elim _ _ _ = raise Match
end
