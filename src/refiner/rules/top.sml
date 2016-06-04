structure TopRules : TOP_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun IsType _ (H >> TYPE (ty, EXP)) =
    let
      val Syn.TOP _ = Syn.out ty
    in
      (T.empty, fn rho =>
        abtToAbs @@
          Syn.into Syn.LBASE)
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val (Syn.TOP tau1, Syn.TOP tau2) = (Syn.out m, Syn.out n)
      val Syn.UNIV (_, i) = Syn.out a
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (_, _, a)) =
    let
      val Syn.TOP _ = Syn.out a
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match
end
