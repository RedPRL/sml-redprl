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
      val (tau1, tau2) = (destBase m, destBase n)
      val i = destUniv a
    in
      (T.empty, fn rho =>
        abtToAbs (check' (CTT AX $ [], TRIV)))
    end

  fun MemberEq alpha (H >> (P, _)) =
    let
      val (tau, m,n,a) = destEq P

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
        abtToAbs (check' (CTT AX $ [], TRIV)))
    end

  fun Elim h alpha (H >> (P, sigma)) =
    let
      val (base, tau) = Ctx.lookup (#hypctx H) h
      val _ = destBase base
      val htm = check' (`h, tau)

      val z = alpha 0
      val ctx' =
        Ctx.interposeAfter
          (#hypctx H)
          (h, Ctx.snoc Ctx.empty (z, (makeCEquiv (#metactx H) (htm, htm), TRIV)))
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = ctx'}
      val goal =
        (newMeta "",
         H' >> (P, sigma))
      val psi = T.snoc T.empty goal
    in
      (psi, fn rho =>
        mapAbs (subst (makeAx, z)) (T.lookup rho (#1 goal)))
    end
end
