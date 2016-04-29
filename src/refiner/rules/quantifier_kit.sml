structure QuantifierKit : QUANTIFIER_KIT =
struct
  open RefinerKit SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  local
    exception Mismatch
  in
    fun destQuantifier theta m =
      (case out m of
           theta' $ [_ \ a, (_, [x]) \ b] =>
             if Operator.eq (fn _ => true) (theta, Operator.map (fn _ => ()) theta') then
               (a, x, b)
             else
               raise Mismatch
         | _ => raise Mismatch)
      handle Mismatch =>
        raise Fail
          @@ "Expected "
           ^ Operator.toString (fn _ => "-") theta
           ^ " but got "
           ^ DebugShowAbt.toString m
  end

  fun TypeEq theta alpha (G |> H >> TRUE (P, _)) =
    let
      val (_, quant1, quant2, univ) = destEq P
      val _ = destUniv univ
      val (a1, x, b1x) = destQuantifier theta quant1
      val (a2, y, b2y) = destQuantifier theta quant2

      val (goal1, _, H) =
        makeGoal @@
          [] |> makeEqSequent H (a1,a2,univ)

      val z = alpha 0
      val ztm = check' (`z, EXP)
      val b1z = subst (ztm, x) b1x
      val b2z = subst (ztm, y) b2y

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a1, EXP)) H

      val (goal2, _, H') =
        makeGoal @@
          [(z,EXP)] |> makeEqSequent H' (b1z, b2z, univ)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ _ = raise Match
end

