structure CEquivRules : CEQUIV_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ @>
  infix 4 >>
  infix 3 |>

  fun IsType alpha (H >> TYPE (ceq, _)) =
    let
      val Syn.CEQUIV (tau, m, n) = Syn.out ceq
      val base = Syn.into @@ Syn.BASE tau
      val (goal1, _, H') =
        makeGoal @@
          H >> MEM (m, base)
      val (goal2, _, H'') =
        makeGoal @@
          H >> MEM (n, base)
      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.LBASE)
    end
    | IsType _ _ = raise Match

  fun TypeEq _ (H >> EQ_MEM (ceq1, ceq2, univ)) =
    let
      val Syn.UNIV (_, i) = Syn.out univ
      val Syn.CEQUIV (tau1, m1, n1) = Syn.out ceq1
      val Syn.CEQUIV (tau2, m2, n2) = Syn.out ceq2
      val () = if tau1 = tau2 then () else raise Fail "CEquiv.TypeEq: sort mismatch"

      val (goal1, _, H) =
        makeGoal @@
          H >> TRUE (Syn.into @@ Syn.CEQUIV (tau1, m1, m2), EXP)

      val (goal2, _, _) =
        makeGoal @@
         H >> TRUE (Syn.into @@ Syn.CEQUIV (tau1, n1, n2), EXP)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq _ (H >> EQ_MEM (m, n, ty)) =
    let
      val Syn.CEQUIV _ = Syn.out ty
      val Syn.AX = Syn.out m
      val Syn.AX = Syn.out n
      val (goal, _, _) =
        makeGoal @@
          H >> TRUE (ty, EXP)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  fun CSym _ (H >> TRUE (P, _)) =
    let
      val Syn.CEQUIV (tau, m, n) = Syn.out P
      val (subgoal, _, _) =
        makeGoal @@
          H >> TRUE (Syn.into @@ Syn.CEQUIV (tau, n,m), EXP)
      val psi = T.empty @> subgoal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | CSym _ _ = raise Match

  fun CStep sign i _ (H >> TRUE (P, _)) =
    let
      val Syn.CEQUIV (tau, m, n) = Syn.out P
      val m' = RedPrlDynamics.stepN sign i m
    in
      (if RedPrlAbt.eq (m', n) then
        (T.empty, fn rho =>
          abtToAbs @@ Syn.into Syn.AX)
       else
         let
           val (subgoal, _, _) =
             makeGoal @@
               H >> TRUE (Syn.into @@ Syn.CEQUIV (tau, m', n), EXP)
           val psi = T.empty @> subgoal
         in
           (psi, fn rho =>
             abtToAbs @@ Syn.into Syn.AX)
         end)
    end
    | CStep _ _ _ _ = raise Match

  fun CEval sign _ (H >> TRUE (P, _)) =
    let
      val Syn.CEQUIV (tau, m, n) = Syn.out P
      val m' = RedPrlDynamics.eval sign m
    in
      (if RedPrlAbt.eq (m', n) then
        (T.empty, fn rho =>
          abtToAbs @@ Syn.into Syn.AX)
       else
         let
           val (subgoal, _, _) =
             makeGoal @@
               H >> TRUE (Syn.into @@ Syn.CEQUIV (tau, m', n), EXP)
           val psi = T.empty @> subgoal
         in
           (psi, fn rho =>
             abtToAbs @@ Syn.into Syn.AX)
         end)
    end
    | CEval _ _ _ = raise Match
end
