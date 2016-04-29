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

  fun TypeEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (tau, m,n,a) = destEq P
      val (tau1, tau2) = (destTop m, destTop n)
      val i = destUniv a
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_,_,_,a) = destEq P
      val _ = destTop a
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | MemberEq _ _ = raise Match
end
