structure MemRules : MEM_RULES =
struct
  open RefinerKit
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun Intro alpha (H >> MEM (m, a)) =
    let
      val (goal, _, _) =
        makeGoal @@
          H >> EQ_MEM (m, m, a)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        T.lookup rho (#1 goal))
    end
    | Intro _ _ = raise Match
end
