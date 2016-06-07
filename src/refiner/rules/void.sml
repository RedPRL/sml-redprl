structure VoidRules : VOID_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 0 $ $# \ @>
  infix 4 >>
  infix 3 |>

  fun TypeEq _ (H >> EQ_MEM (void1, void2, univ)) =
    let
      val Syn.UNIV _ = Syn.out univ
      val Syn.VOID = Syn.out void1
      val Syn.VOID = Syn.out void2
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun Elim i _ (H >> TRUE (P, _)) =
    let
      val (void, _) = Ctx.lookup (getHyps H) i
      val Syn.VOID = Syn.out void
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | Elim _ _ _ = raise Match

end
