structure VoidRules : VOID_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ >> $ $# \ @>

  fun destVoid m =
    case out m of
         CTT VOID $ [] => ()
       | _ =>
           raise Fail
             @@ "Expected Void but got "
              ^ DebugShowAbt.toString m

  fun TypeEq _ (H >> TRUE (P, _)) =
    let
      val (_, void1, void2, univ) = destEq P
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
      val (void, _) = Ctx.lookup (#hypctx H) i
      val _ = destVoid void
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | Elim _ _ _ = raise Match

end
