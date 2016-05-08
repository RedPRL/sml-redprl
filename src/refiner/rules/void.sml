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

  fun TypeEq _ (H >> EQ_MEM (void1, void2, univ)) =
    let
      val _ = destUniv univ
      val _ = destVoid void1
      val _ = destVoid void2
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun Elim i _ (H >> TRUE (P, _)) =
    let
      val (void, _) = Ctx.lookup (getHyps H) i
      val _ = destVoid void
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | Elim _ _ _ = raise Match

end
