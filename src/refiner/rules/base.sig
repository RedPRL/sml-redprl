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

  fun TypeEq alpha (H >> P) =
    let
      val (m,n,a) = destEq P
      val (tau1, tau2) = (destBase m, destBase n)
      val i = destUniv a
    in
      (T.empty, fn rho =>
        abtToAbs (check' (CTT AX $ [], EXP)))
    end

  fun MemberEq alpha (H >> P) =
    let
      val (m,n,a) = destEq P
      val tau = destBase a
      val psi = metactx P
      val subgoals =
        VarCtx.foldl
          (fn (x, tau, tl) =>
            let
              val meta = newMeta ("base_" ^ Variable.toString x)
              val xtm = check' (`x, tau)
              val base = check' (CTT (BASE tau) $ [], EXP)
              val goal = check' (CTT (MEMBER tau) $ [([],[]) \ xtm, ([],[]) \ base], EXP)
            in
              T.snoc tl (meta, H >> goal)
            end)
          T.empty
          (varctx m)
      val mainGoal = check psi (CTT (CEQUIV tau) $ [([],[]) \ m, ([],[]) \ n], EXP)
      val subgoals' = T.snoc subgoals (newMeta "ceq", H >> mainGoal)
    in
      (subgoals', fn rho =>
        abtToAbs (check' (CTT AX $ [], EXP)))
    end
end
