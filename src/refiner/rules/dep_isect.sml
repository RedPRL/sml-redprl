structure DepIsectRules : DEP_ISECT_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData

  infix @@ $ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  val destDepIsect =
    QuantifierKit.destQuantifier (CTT DEP_ISECT)

  val IsType =
    QuantifierKit.IsType (CTT DEP_ISECT)

  val TypeEq =
    QuantifierKit.TypeEq (CTT DEP_ISECT)

  fun MemberEq alpha (G |> H >> EQ_MEM (m1, m2, ty)) =
    let
      val (a, x, bx) = destDepIsect ty
      val bm1 = subst (m1, x) bx

      val (goal1, _, H') =
        makeGoal @@
          [] |> makeEqSequent H (m1, m2, a)

      val (goal2, _, _) =
        makeGoal @@
          [] |> makeEqSequent H' (m1, m2, bm1)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | MemberEq _ _ = raise Match
end
