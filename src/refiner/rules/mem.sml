structure MemRules : MEM_RULES =
struct
  open RefinerKit OperatorData CttOperatorData RecordOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun Intro alpha (G |> H >> MEM (m, a)) =
    let
      val (goal, _, _) =
        makeGoal @@
          [] |> H >> EQ_MEM (m, m, a)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        makeEvidence G H @@
          T.lookup rho (#1 goal) // ([],[]))
    end
    | Intro _ _ = raise Match
end
