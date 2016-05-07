structure TopRules : TOP_RULES =
struct
  open RefinerKit OperatorData CttOperatorData LevelOperatorData SortData
  infix @@ $ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun destTop m =
    case out m of
         CTT (TOP tau) $ _ => tau
       | _ =>
           raise Fail
             @@ "Expected Top but got "
              ^ DebugShowAbt.toString m

  fun IsType _ (G |> H >> TYPE (ty, EXP)) =
    let
      val _ = destTop ty
    in
      (T.empty, fn rho =>
        makeEvidence G H @@
          check' (LVL_OP LBASE $ [], LVL))
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (G |> H >> EQ_MEM (m, n, a)) =
    let
      val (tau1, tau2) = (destTop m, destTop n)
      val i = destUniv a
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (G |> H >> EQ_MEM (_, _, a)) =
    let
      val _ = destTop a
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | MemberEq _ _ = raise Match
end
