structure BaseRules : BASE_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun IsType _ (H >> TYPE (ty, EXP)) =
    let
      val Syn.BASE _ = Syn.out ty
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.LBASE)
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val (Syn.BASE tau1, Syn.BASE tau2) = (Syn.out m, Syn.out n)
      val Syn.UNIV (_, i) = Syn.out a
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val Syn.BASE tau = Syn.out a
      val subgoals =
        VarCtx.foldl
          (fn (x, RS.EXP tau, tl) =>
                let
                  val meta = newMeta ""
                  val xtm = check (`x, RS.EXP tau)
                  val goal = Syn.into @@ Syn.MEMBER (tau, xtm, a)
                in
                  tl @> (meta, H >> TRUE (goal, EXP))
                end
            | _ => raise Match)
          T.empty
          (varctx m)

      val (mainGoal, _, _) =
        makeGoal @@
          H >> TRUE (Syn.into @@ Syn.CEQUIV (tau, m, n), EXP)

      val subgoals' = subgoals @> mainGoal
    in
      (subgoals', fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  fun Elim h alpha (H >> TRUE (P, sigma)) =
    let
      val (base, tau) = Ctx.lookup (getHyps H) h
      val Syn.BASE _ = Syn.out base
      val htm = check (`h, RS.EXP tau)

      val z = alpha 0
      val ctx' =
        Ctx.interposeAfter
          (getHyps H)
          (h, Ctx.snoc Ctx.empty z (Syn.into @@ Syn.CEQUIV (tau, htm, htm), EXP))

      val H' = updateHyps (fn _ => ctx') H

      val (goal, _, _) =
        makeGoal @@
          ([], [(z,EXP)]) |> H' >> TRUE (P, sigma)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@
          T.lookup rho (#1 goal) // ([], [Syn.into Syn.AX]))
    end
    | Elim _ _ _ = raise Match
end
