structure CEquivRules : CEQUIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix >> $ \

  fun TypeEq _ (H >> (P, _)) =
    let
      val (_, ceq1, ceq2, univ) = destEq P
      val i = destUniv univ
      val (tau1, m1, n1) = destCEquiv ceq1
      val (tau2, m2, n2) = destCEquiv ceq2
      val () = if tau1 = tau2 then () else raise Fail "CEquiv.TypeEq: sort mismatch"
      val goal1 =
        (newMeta "",
         H >> (makeCEquiv (#metactx H) (m1, m2), TRIV))
      val goal2 =
        (newMeta "",
         H >> (makeCEquiv (#metactx H) (n1, n2), TRIV))
      val psi = T.snoc (T.snoc T.empty goal1) goal2
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end

  fun CSym _ (H >> (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val x = newMeta ""
      val subgoal = makeCEquiv (#metactx H) (n,m)
      val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end

  fun CStep sign i _ (H >> (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val m' = DynamicsUtil.stepn sign i m
    in
      (if Abt.eq (m', n) then
        (T.empty, fn rho =>
          abtToAbs makeAx)
       else
         let
           val x = newMeta ""
           val subgoal = makeCEquiv (#metactx H) (m', n)
           val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
         in
           (psi, fn rho =>
             abtToAbs makeAx)
         end)
    end

  fun CEval sign _ (H >> (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val m' = DynamicsUtil.evalOpen sign m
    in
      (if Abt.eq (m', n) then
        (T.empty, fn rho =>
          abtToAbs makeAx)
       else
         let
           val x = newMeta ""
           val subgoal = makeCEquiv (#metactx H) (m', n)
           val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
         in
           (psi, fn rho =>
             abtToAbs makeAx)
         end)
    end
end
