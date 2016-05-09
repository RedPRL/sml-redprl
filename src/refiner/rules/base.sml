structure BaseRules : BASE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix 0 @@
  infix 1 $ $$ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun destBase m =
    case out m of
         CTT (BASE tau) $ _ => tau
       | _ =>
           raise Fail
             @@ "Expected Base but got "
              ^ DebugShowAbt.toString m

  fun IsType _ (H >> TYPE (ty, EXP)) =
    let
      val _ = destBase ty
    in
      (T.empty, fn rho =>
        abtToAbs @@
          LVL_OP LBASE $$ [])
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val (tau1, tau2) = (destBase m, destBase n)
      val i = destUniv a
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val tau = destBase a
      val subgoals =
        VarCtx.foldl
          (fn (x, tau, tl) =>
            let
              val meta = newMeta ""
              val xtm = check (`x, tau)
              val base = CTT (BASE tau) $$ []
              val goal = CTT (MEMBER tau) $$ [([],[]) \ xtm, ([],[]) \ base]
            in
              tl @> (meta, H >> TRUE (goal, EXP))
            end)
          T.empty
          (varctx m)

      val (mainGoal, _, _) =
        makeGoal @@
          H >> TRUE (CTT (CEQUIV tau) $$ [([],[]) \ m, ([],[]) \ n], EXP)

      val subgoals' = subgoals @> mainGoal
    in
      (subgoals', fn rho =>
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  fun Elim h alpha (H >> TRUE (P, sigma)) =
    let
      val (base, tau) = Ctx.lookup (getHyps H) h
      val _ = destBase base
      val htm = check (`h, tau)

      val z = alpha 0
      val ctx' =
        Ctx.interposeAfter
          (getHyps H)
          (h, Ctx.snoc Ctx.empty z (makeCEquiv (htm, htm), EXP))

      val H' = updateHyps (fn _ => ctx') H

      val (goal, _, _) =
        makeGoal @@
          [(z,EXP)] |> H' >> TRUE (P, sigma)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@
          T.lookup rho (#1 goal) // ([], [makeAx]))
    end
    | Elim _ _ _ = raise Match
end
