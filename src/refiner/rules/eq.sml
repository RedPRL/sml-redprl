structure EqRules : EQ_RULES =
struct
  open RefinerKit
  infix @@ $ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

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
