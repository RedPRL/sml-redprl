structure SquashRules : SQUASH_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ \ @>
  infix 4 >>
  infix 3 |>

  fun destSquash m =
    case out m of
         CTT (SQUASH tau) $ [_\a] => (tau, a)
       | _ =>
           raise Fail
             @@ "Expected Squash but got "
              ^ DebugShowAbt.toString m

  fun TypeEq _ (G |> H >> TRUE (P, _)) =
    let
      val (tau,a,b,univ) = destEq P
      val (_, a') = destSquash a
      val (_, b') = destSquash b
      val _ = destUniv univ
      val goal =
        check
          (#metactx H)
          (CTT (EQ tau) $ [([],[]) \ a', ([],[]) \ b', ([],[]) \ univ], EXP)
      val psi = T.empty @> (newMeta "", [] |> H >> TRUE (goal, EXP))
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

  fun Intro _ (G |> H >> TRUE (P, _)) =
    let
      val (tau, Q) = destSquash P
      val psi = T.empty @> (newMeta "", [] |> H >> TRUE (Q, tau))
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | Intro _ _ = raise Match

  fun Unhide h _ (G |> H >> TRUE (P, tau)) =
    let
      val _ = destEq P
      val (Q, sigma) = Ctx.lookup (#hypctx H) h
      val (tau', Q') = destSquash Q
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.modify h (fn _ => (Q', tau')) (#hypctx H)}

      val x = newMeta ""
      val psi = T.empty @> (x, [] |> H' >> TRUE (P, tau))
    in
      (psi, fn rho =>
        let
          val _ \ ev = outb @@ T.lookup rho x
        in
          makeEvidence G H ev
        end)
    end
    | Unhide _ _ _ = raise Match

end
