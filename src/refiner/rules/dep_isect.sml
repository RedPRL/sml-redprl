structure DepIsectRules : DEP_ISECT_RULES =
struct
  open RefinerKit SortData

  infixr 0 @@
  infix 0 $ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun destDepIsect m =
    case Syn.out m of
       Syn.DEP_ISECT (a, x, bx) => (a, x, bx)
     | _ => raise Match

  val IsType =
    QuantifierKit.IsType destDepIsect

  val TypeEq =
    QuantifierKit.TypeEq destDepIsect

  fun MemberEq alpha (H >> EQ_MEM (m1, m2, ty)) =
    let
      val (a, x, bx) = destDepIsect ty
      val bm1 = subst (m1, x) bx

      val (goal1, _, H') =
        makeGoal @@
          makeEqSequent H (m1, m2, a)

      val (goal2, _, _) =
        makeGoal @@
          makeEqSequent H' (m1, m2, bm1)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match
end
