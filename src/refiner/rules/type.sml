structure TypeRules : TYPE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix $ $# \ @> @@
  infix 4 >>
  infix 3 |>

  fun Intro _ (G |> H >> TYPE (P, tau)) =
    let
      val (lvlGoal, lvlHole, H) =
        makeGoal @@
          [] |> makeLevelSequent H

      val univ =
        check
          (#metactx H)
          (CTT (UNIV tau) $ [([],[]) \ lvlHole [] []],
           EXP)

      val (memGoal, _, _)  =
        makeGoal @@
          [] |> makeMemberSequent H (P, univ)

      val psi = T.empty @> lvlGoal @> memGoal
    in
      (psi, fn rho =>
        let
          val _ \ lvl = outb @@ T.lookup rho (#1 lvlGoal)
        in
          makeEvidence G H lvl
        end)
    end
    | Intro _ _ = raise Match
end
