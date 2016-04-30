structure TypeRules : TYPE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix $ $# \ @> @@
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun Intro _ (G |> H >> TYPE (a, tau)) =
    let
      val (lvlGoal, lvlHole, H') =
        makeGoal @@
          [] |> makeLevelSequent H

      val H'' = updateMetas (fn _ => getMetas H') H

      val univ =
        check
          (getMetas H)
          (CTT (UNIV tau) $ [([],[]) \ lvlHole [] []],
           EXP)

      val (memGoal, _, _)  =
        makeGoal @@
          [] |> makeMemberSequent H'' (a, univ)

      val psi = T.empty @> lvlGoal @> memGoal
    in
      (psi, fn rho =>
        makeEvidence G H @@
          T.lookup rho (#1 lvlGoal) // ([],[]))
    end
    | Intro _ _ = raise Match

  fun Synth _ (G |> H >> SYN r) =
    let
      val (lvlGoal, _, _) =
        makeGoal @@
          [] |> H >> TYPE (r, EXP)
      val psi = T.empty @> lvlGoal
    in
      (psi, fn rho =>
        let
          val lvl = T.lookup rho (#1 lvlGoal) // ([],[])
        in
          makeEvidence G H @@
            makeUniv lvl
        end)
    end
    | Synth _ _ = raise Match
end
