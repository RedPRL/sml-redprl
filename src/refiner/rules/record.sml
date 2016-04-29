structure RecordRules : RECORD_RULES =
struct
  open RefinerKit OperatorData CttOperatorData RecordOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun destRecord m =
    case out m of
         RCD RECORD $ [_ \ desc] => desc
       | _ =>
           raise Fail
             @@ "Expected RECORD but got "
              ^ DebugShowAbt.toString m

  fun destRecordDesc m =
    case out m of
         RCD RECORD_DESC $ [_ \ lvl] => lvl
       | _ =>
           raise Fail
             @@ "Expected RECORD_DESC but got "
              ^ DebugShowAbt.toString m

  fun destDescNil m =
    case out m of
         RCD DESC_NIL $ _ => ()
       | _ =>
           raise Fail
             @@ "Expected DESC_NIL but got "
              ^ DebugShowAbt.toString m

  fun destDescCons m =
    case out m of
         RCD (DESC_CONS lbl) $ [_ \ a, (_, [x]) \ b] => (lbl, a, x, b)
       | _ =>
           raise Fail
             @@ "Expected DESC_NIL but got "
              ^ DebugShowAbt.toString m

  fun makeRecordDesc lvl =
    check
      (metactx lvl)
      (RCD RECORD_DESC $ [([],[]) \ lvl],
       EXP)

  fun DescNilEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_,d1,d2,ty) = destEq P
      val _ = destRecordDesc ty
      val () = destDescNil d1
      val () = destDescNil d2
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | DescNilEq _ _ = raise Match

  fun DescConsEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_,d1,d2,ty) = destEq P
      val lvl = destRecordDesc ty
      val (lbl1, a1, x1, d1) = destDescCons d1
      val (lbl2, a2, x2, d2) = destDescCons d2
      val _ = if Symbol.eq (lbl1, lbl2) then () else raise Match

      val z = alpha 0
      val d1z = subst (check' (`z, EXP), x1) d1
      val d2z = subst (check' (`z, EXP), x2) d2

      val (goal1, _, H') =
        makeGoal @@
          [] |> makeEqSequent H (a1, a2, makeUniv lvl)

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a1, EXP)) H

      val (goal2, _, _) =
        makeGoal @@
          [(z, EXP)] |> makeEqSequent H' (d1z, d2z, makeRecordDesc lvl)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | DescConsEq _ _ = raise Match

  fun TypeEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_,t1,t2,univ) = destEq P
      val (tau, lvl) = destUniv univ
      val _ = if Sort.eq (tau, EXP) then () else raise Match
      val desc1 = destRecord t1
      val desc2 = destRecord t2

      val (goal, _, _) =
        makeGoal @@
          [] |> makeEqSequent H (desc1, desc2, makeRecordDesc lvl)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

end
