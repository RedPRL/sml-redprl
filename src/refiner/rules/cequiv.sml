structure CEquivRules : CEQUIV_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix $ \ @> @@
  infix 4 >>
  infix 3 |>

  fun TypeEq _ (G |> H >> EQ_MEM (ceq1, ceq2, univ)) =
    let
      val i = destUniv univ
      val (tau1, m1, n1) = destCEquiv ceq1
      val (tau2, m2, n2) = destCEquiv ceq2
      val () = if tau1 = tau2 then () else raise Fail "CEquiv.TypeEq: sort mismatch"

      val (goal1, _, H) =
        makeGoal @@
          [] |> H >> TRUE (makeCEquiv (getMetas H) (m1, m2), EXP)

      val (goal2, _, _) =
        makeGoal @@
         [] |> H >> TRUE (makeCEquiv (getMetas H) (n1, n2), EXP)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq _ (G |> H >> EQ_MEM (m, n, ty)) =
    let
      val _ = destCEquiv ty
      val _ = destAx m
      val _ = destAx n
      val (goal, _, _) =
        makeGoal @@
          [] |> H >> TRUE (ty, EXP)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | MemberEq _ _ = raise Match

  fun CSym _ (G |> H >> TRUE (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val (subgoal, _, _) =
        makeGoal @@
          [] |> H >> TRUE (makeCEquiv (getMetas H) (n,m), EXP)
      val psi = T.empty @> subgoal
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | CSym _ _ = raise Match

  fun CStep sign i _ (G |> H >> TRUE (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val m' = DynamicsUtil.stepn sign i m
    in
      (if Abt.eq (m', n) then
        (T.empty, fn rho =>
          makeEvidence G H makeAx)
       else
         let
           val (subgoal, _, _) =
             makeGoal @@
               [] |> H >> TRUE (makeCEquiv (getMetas H) (m', n), EXP)
           val psi = T.empty @> subgoal
         in
           (psi, fn rho =>
             makeEvidence G H makeAx)
         end)
    end
    | CStep _ _ _ _ = raise Match

  fun CEval sign _ (G |> H >> TRUE (P, _)) =
    let
      val (tau, m, n) = destCEquiv P
      val m' = DynamicsUtil.evalOpen sign m
    in
      (if Abt.eq (m', n) then
        (T.empty, fn rho =>
          makeEvidence G H makeAx)
       else
         let
           val (subgoal, _, _) =
             makeGoal @@
               [] |> H >> TRUE (makeCEquiv (getMetas H) (m', n), EXP)
           val psi = T.empty @> subgoal
         in
           (psi, fn rho =>
             makeEvidence G H makeAx)
         end)
    end
    | CEval _ _ _ = raise Match
end
