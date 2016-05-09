structure SquashRules : SQUASH_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun destSquash m =
    case out m of
         CTT (SQUASH tau) $ [_\a] => (tau, a)
       | _ =>
           raise Fail
             @@ "Expected Squash but got "
              ^ DebugShowAbt.toString m

  fun TypeEq _ (H >> EQ_MEM (a,b,univ)) =
    let
      val (_, a') = destSquash a
      val (_, b') = destSquash b
      val (tau, _) = destUniv univ
      val eq = check (CTT (EQ tau) $ [([],[]) \ a', ([],[]) \ b', ([],[]) \ univ], EXP)
      val (goal, _, _) =
        makeGoal @@
          H >> TRUE (eq, EXP)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun Intro _ (H >> TRUE (P, _)) =
    let
      val (tau, Q) = destSquash P
      val (goal, _, _) =
        makeGoal @@
          H >> TRUE (Q, tau)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | Intro _ _ = raise Match

  fun Unhide h _ (H >> EQ_MEM (m, n, a)) =
    let
      val (Q, sigma) = Ctx.lookup (getHyps H) h
      val (tau', Q') = destSquash Q
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
