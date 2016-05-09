structure GenericRules : GENERIC_RULES =
struct
  open RefinerKit OperatorData CttOperatorData RecordOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun Intro alpha (G |> jdg) =
    let
      val (goal, _, _) =
        makeGoal jdg
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        let
          val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb @@ T.lookup rho (#1 goal)
          val (xs', taus') = ListPair.unzip G
        in
          checkb
            ((us, xs' @ xs) \ m,
             ((sigmas, taus' @ taus), tau))
        end)
    end
    | Intro _ _ = raise Match
end
