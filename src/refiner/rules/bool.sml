structure BoolRules :> BOOL_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun IsType _ (H >> TYPE (ty, EXP)) =
    let
      val Syn.BOOL = Syn.out ty
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.LBASE)
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val (Syn.BOOL, Syn.BOOL) = (Syn.out m, Syn.out n)
      val Syn.UNIV (_, i) = Syn.out a
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (m, n, a)) =
    let
      val Syn.BOOL = Syn.out a
      val () =
        case (Syn.out m, Syn.out n) of
           (Syn.BOOL_TT, Syn.BOOL_TT) => ()
         | (Syn.BOOL_FF, Syn.BOOL_FF) => ()
         | _ => raise Match
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  fun Elim z alpha (H >> TRUE (ty, EXP)) =
    let
      val (bool, _) = Ctx.lookup (getHyps H) z
      val Syn.BOOL = Syn.out bool

      val tyT = subst (Syn.into Syn.BOOL_TT, z) ty
      val tyF = subst (Syn.into Syn.BOOL_FF, z) ty

      val (goalT, _, _) =
        makeGoal @@
          H >> TRUE (tyT, EXP)

      val (goalF, _, _) =
        makeGoal @@
          H >> TRUE (tyF, EXP)

      val psi = T.empty @> goalT @> goalF
    in
      (psi, fn rho =>
         let
           val t = T.lookup rho (#1 goalT) // ([],[])
           val f = T.lookup rho (#1 goalF) // ([],[])
         in
           abtToAbs @@ Syn.into @@ Syn.BOOL_IF ((z, ty), Syn.var (z, EXP), t, f)
         end)
    end
    | Elim _ _ _ = raise Match
end
