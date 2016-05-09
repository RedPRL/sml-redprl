structure TypeRules : TYPE_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix 0 @@
  infix 1 $ $$ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun Intro _ (H >> TYPE (a, tau)) =
    let
      val (lvlGoal, lvlHole, H') =
        makeGoal @@
          makeLevelSequent H

      val univ = CTT (UNIV tau) $$ [([],[]) \ lvlHole [] []]

      val (memGoal, _, _)  =
        makeGoal @@
          makeMemberSequent H' (a, univ)

      val psi = T.empty @> lvlGoal @> memGoal
    in
      (psi, fn rho =>
        T.lookup rho (#1 lvlGoal))
    end
    | Intro _ _ = raise Match

  fun Synth _ (H >> TYPE (a, tau)) =
    let
      val (univGoal, _, _) =
        makeGoal @@
          H >> SYN a
      val psi = T.empty @> univGoal
    in
      (psi, fn rho =>
         let
           val univ = T.lookup rho (#1 univGoal) // ([],[])
           val lvl = CTT UNIV_GET_LVL $$ [([],[]) \ univ]
         in
           abtToAbs lvl
         end)
    end
    | Synth _ _ = raise Match
end
