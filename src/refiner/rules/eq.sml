structure EqRules : EQ_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun Intro alpha (G |> H >> TRUE (P, _)) =
    let
      val (_, m, n, a) = destEq P
      val (goal, _, _) =
        makeGoal @@
          G |> H >> EQ_MEM (m, n, a)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
         T.lookup rho (#1 goal))
    end
    | Intro _ _ = raise Match

end
