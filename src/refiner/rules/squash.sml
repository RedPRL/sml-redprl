structure SquashRules : SQUASH_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ \ >>

  fun destSquash m =
    case out m of
         CTT (SQUASH tau) $ [_\a] => (tau, a)
       | _ =>
           raise Fail
             @@ "Expected Squash but got "
              ^ DebugShowAbt.toString m

  fun TypeEq _ (H >> TRUE (P, _)) =
    let
      val (tau,a,b,univ) = destEq P
      val (_, a') = destSquash a
      val (_, b') = destSquash b
      val _ = destUniv univ
      val goal =
        check
          (#metactx H)
          (CTT (EQ tau) $ [([],[]) \ a', ([],[]) \ b', ([],[]) \ univ], EXP)
      val psi = T.snoc T.empty (newMeta "", H >> TRUE (goal, EXP))
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun Intro _ (H >> TRUE (P, _)) =
    let
      val (tau, Q) = destSquash P
      val psi = T.snoc T.empty (newMeta "", H >> TRUE (Q, tau))
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | Intro _ _ = raise Match

  fun Unhide h _ (H >> TRUE (P, tau)) =
    let
      val _ = destEq P
      val (Q, sigma) = Ctx.lookup (#hypctx H) h
      val (tau', Q') = destSquash Q
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.modify (#hypctx H) (h, fn _ => (Q', tau'))}

      val x = newMeta ""
      val psi = T.snoc T.empty (x, H' >> TRUE (P, tau))
    in
      (psi, fn rho =>
        T.lookup rho x)
    end
    | Unhide _ _ _ = raise Match

end
