structure TopRules : TOP_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
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
