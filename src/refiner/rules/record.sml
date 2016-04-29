structure RecordRules : RECORD_RULES =
struct
  open RefinerKit OperatorData CttOperatorData RecordOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun destRecord m =
    case out m of
         RCD (RECORD lbl) $ [_ \ a, (_, [x]) \ b] => (lbl, a, x, b)
       | _ =>
           raise Fail
             @@ "Expected RECORD but got "
              ^ DebugShowAbt.toString m

  fun TypeEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_,ty1,ty2,univ) = destEq P
      val (tau, lvl) = destUniv univ
      val _ = if Sort.eq (tau, EXP) then () else raise Match

      val (lbl1, a1, x1, b1) = destRecord ty1
      val (lbl2, a2, x2, b2) = destRecord ty2
      val _ = if Symbol.eq (lbl1, lbl2) then () else raise Match

      val z = alpha 0
      val b1z = subst (check' (`z, EXP), x1) b1
      val b2z = subst (check' (`z, EXP), x2) b2

      val (goal1, _, H') =
        makeGoal @@
          [] |> makeEqSequent H (a1, a2, makeUniv lvl)

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a1, EXP)) H

      val (goal2, _, _) =
        makeGoal @@
          [(z, EXP)] |> makeEqSequent H' (b1z, b2z, makeUniv lvl)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

end
