structure VoidRules : VOID_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ $# \ @>
  infix 4 >>
  infix 3 |>

  fun destVoid m =
    case out m of
         CTT VOID $ [] => ()
       | _ =>
           raise Fail
             @@ "Expected Void but got "
              ^ DebugShowAbt.toString m

  fun TypeEq _ (G |> H >> TRUE (P, _)) =
    let
      val (_, void1, void2, univ) = destEq P
      val _ = destUniv univ
      val _ = destVoid void1
      val _ = destVoid void2
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

  fun Elim i _ (G |> H >> TRUE (P, _)) =
    let
      val (void, _) = Ctx.lookup (#hypctx H) i
      val _ = destVoid void
    in
      (T.empty, fn rho =>
        makeEvidence G H makeAx)
    end
    | Elim _ _ _ = raise Match

end
