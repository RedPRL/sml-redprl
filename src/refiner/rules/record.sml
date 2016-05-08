structure RecordRules : RECORD_RULES =
struct
  open RefinerKit OperatorData CttOperatorData RecordOperatorData LevelOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun destSingl m =
    case out m of
         RCD (SINGL lbl) $ [_ \ a] => (lbl, a)
       | _ =>
           raise Fail
             @@ "Expected SINGL but got "
              ^ DebugShowAbt.toString m

  fun destProj m =
    case out m of
         RCD (PROJ lbl) $ [_ \ rcd] => (lbl, rcd)
       | _ =>
           raise Fail
             @@ "Expected PROJ but got "
              ^ DebugShowAbt.toString m

  fun makeProj lbl m =
    check
      (metactx m)
      (RCD (PROJ lbl) $ [([],[]) \ m], EXP)

  fun IsType alpha (goal as (H >> TYPE (ty, EXP))) =
    let
      val (lbl, a) = destSingl ty

      val (goalA, holeA, H') =
        makeGoal @@
          H >> TYPE (a, EXP)

      val psi = T.empty @> goalA
    in
      (psi, fn rho =>
          T.lookup rho (#1 goalA))
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (H >> EQ_MEM (ty1, ty2, univ)) =
    let
      val (tau, lvl) = destUniv univ
      val _ = if Sort.eq (tau, EXP) then () else raise Match

      val (lbl1, a1) = destSingl ty1
      val (lbl2, a2) = destSingl ty2
      val _ = if Symbol.eq (lbl1, lbl2) then () else raise Match

      val (goal, _, _) =
        makeGoal @@
          makeEqSequent H (a1, a2, makeUniv lvl)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (rcd1, rcd2, ty)) =
    let
      val (lbl, a) = destSingl ty

      val proj1 = makeProj lbl rcd1
      val proj2 = makeProj lbl rcd2

      val (goal, _, _) =
        makeGoal @@
          makeEqSequent H (proj1, proj2, a)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  (* H >> R.lbl synth ~> A
   *   H >> R synth ~> singl[lbl](A)
   *)
  fun ProjSynth alpha (H >> SYN p) =
    let
      val (lbl, rcd) = destProj p

      val (tyGoal, tyHole, H') =
        makeGoal @@
          H >> SYN rcd

      val psi = T.empty @> tyGoal
    in
      (psi, fn rho =>
        let
          val ty = T.lookup rho (#1 tyGoal) // ([],[])
        in
          abtToAbs @@
            check (metactx ty) (RCD SINGL_GET_TY $ [([],[]) \ ty], EXP)
        end)
    end
    | ProjSynth _ _ = raise Match
end
