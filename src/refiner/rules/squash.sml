structure SquashRules : SQUASH_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun TypeEq _ (H >> EQ_MEM (a,b,univ)) =
    let
      val Syn.SQUASH (_, a') = Syn.out a
      val Syn.SQUASH (_, b') = Syn.out b
      val Syn.UNIV (tau, _) = Syn.out univ
      val eq = Syn.into @@ Syn.EQ (tau, a', b', univ)
      val (goal, _, _) =
        makeGoal @@
          H >> TRUE (eq, EXP)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun Intro _ (H >> TRUE (P, _)) =
    let
      val Syn.SQUASH (tau, Q) = Syn.out P
      val (goal, _, _) =
        makeGoal @@
          H >> TRUE (Q, tau)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | Intro _ _ = raise Match

  fun Unhide h _ (H >> EQ_MEM (m, n, a)) =
    let
      val (Q, sigma) = Ctx.lookup (getHyps H) h
      val Syn.SQUASH (tau', Q') = Syn.out Q
      val H' = updateHyps (Ctx.modify h (fn _ => (Q', tau'))) H

      val (goal, _, _) =
        makeGoal @@
          H' >> EQ_MEM (m, n, a)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        T.lookup rho (#1 goal))
    end
    | Unhide _ _ _ = raise Match

end
