structure SynthRules : SYNTH_RULES =
struct
  open RefinerKit OperatorData CttOperatorData RecordOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun CheckToSynth alpha (G |> H >> EQ_MEM (r, s, a)) =
    let
      val (tyGoal, tyHole, H') =
        makeGoal @@
          [] |> H >> EQ_SYN (r, s)

      val tau = Abt.sort r

      val (lvlGoal, lvlHole, H'') =
        makeGoal @@
          [] |> H' >> TYPE (a, tau)

      val univ =
        check
          (getMetas H'')
          (CTT (UNIV tau) $ [([],[]) \ lvlHole [][]], EXP)

      val (eqGoal, _, _) =
        makeGoal @@
          [] |> H'' >> EQ_MEM (a, tyHole [] [], univ)

      val psi = T.empty @> tyGoal @> lvlGoal @> eqGoal
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | CheckToSynth _ _ = raise Match

  fun SynthEqIntro alpha (G |> H >> EQ_SYN (r, s)) =
    let
      val (rgoal, rhole, H') =
        makeGoal @@
          [] |> H >> SYN r

      val (sgoal, shole, H'') =
        makeGoal @@
          [] |> H' >> SYN s

      val (univGoal, univHole, H''') =
        makeGoal @@
          [] |> H'' >> SYN (rhole [] [])

      val (eqGoal, _, _) =
        makeGoal @@
          [] |> H''' >> EQ_MEM (rhole [] [], shole [] [], univHole [] [])

      val psi = T.empty @> rgoal @> sgoal @> univGoal @> eqGoal
    in
      (psi, fn rho =>
         makeEvidence G H @@
           T.lookup rho (#1 rgoal) // ([],[]))
    end
    | SynthEqIntro _ _ = raise Match

  fun SynthType _ (G |> H >> SYN r) =
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
    | SynthType _ _ = raise Match
end
