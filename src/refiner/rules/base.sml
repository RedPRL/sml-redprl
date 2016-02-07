structure BaseRules : BASE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ >> $ \

  fun destBase m =
    case out m of
         CTT (BASE tau) $ _ => tau
       | _ =>
           raise Fail
             @@ "Expected Base but got "
              ^ DebugShowAbt.toString m

  fun TypeEq alpha (H >> (P, _)) =
    let
      val (tau, m,n,a) = destEq P
      val () = if tau = EXP then () else raise Fail "Expected exp"
      val (tau1, tau2) = (destBase m, destBase n)
      val i = destUniv a
    in
      (T.empty, fn rho =>
        abtToAbs (check' (CTT AX $ [], EXP)))
    end

  fun MemberEq alpha (H >> (P, _)) =
    let
      val (tau, m,n,a) = destEq P
      val () = if tau = EXP then () else raise Fail "Expected exp"

      val tau = destBase a
      val subgoals =
        VarCtx.foldl
          (fn (x, tau, tl) =>
            let
              val meta = newMeta (Variable.toString x)
              val xtm = check' (`x, tau)
              val base = check' (CTT (BASE tau) $ [], EXP)
              val goal = check' (CTT (MEMBER tau) $ [([],[]) \ xtm, ([],[]) \ base], EXP)
            in
              T.snoc tl (meta, H >> (goal, EXP))
            end)
          T.empty
          (varctx m)
      val mainGoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ m, ([],[]) \ n], EXP)
      val subgoals' = T.snoc subgoals (newMeta "", H >> (mainGoal, EXP))
    in
      (subgoals', fn rho =>
        abtToAbs (check' (CTT AX $ [], EXP)))
    end
end
