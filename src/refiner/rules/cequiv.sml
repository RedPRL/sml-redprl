structure CEquivRules : CEQUIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix >> $ \

  fun CSym _ (H >> (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val x = newMeta ""
      val subgoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ n, ([],[]) \ m], EXP)
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
           val subgoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ m', ([],[]) \ n], EXP)
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
           val subgoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ m', ([],[]) \ n], EXP)
           val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
         in
           (psi, fn rho =>
             abtToAbs makeAx)
         end)
    end
end
