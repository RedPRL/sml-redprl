structure EqRules : EQ_RULES =
struct
  open RefinerKit
  infix @@ $ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun IsType alpha (H >> TYPE (P, _)) =
    let
      val Syn.EQ (tau, m, n, a) = Syn.out P
      val (lvlGoal, lvlHole, H') = makeGoal @@ H >> TYPE (a, tau)
      val (goal1, _, _) = makeGoal @@ makeMemberSequent H' (m, a)
      val (goal2, _, _) = makeGoal @@ makeMemberSequent H' (n, a)
      val psi = T.empty @> lvlGoal @> goal1 @> goal2
    in
      (psi, fn rho =>
        T.lookup rho (#1 lvlGoal))
    end

  fun Intro alpha (H >> TRUE (P, _)) =
    let
      val Syn.EQ (_, m, n, a) = Syn.out P

      val (goal, _, _) =
        makeGoal @@
          H >> EQ_MEM (m, n, a)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        T.lookup rho (#1 goal))
    end
    | Intro _ _ = raise Match

end
