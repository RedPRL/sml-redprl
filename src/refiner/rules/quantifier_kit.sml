structure QuantifierKit : QUANTIFIER_KIT =
struct
  open RefinerKit RedPrlAbt
  infixr 0 @@
  infix 1 $ $$ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  type quantifier_destruct = RedPrlAbt.abt -> RedPrlAbt.abt * RedPrlAbt.variable * RedPrlAbt.abt

  fun IsType destruct alpha (goal as (H >> TYPE (ty, EXP))) =
    let
      val (a, x, bx) = destruct ty

      val (goalA, holeA, H') =
        makeGoal @@
          H >> TYPE (a, EXP)

      val Hx = updateHyps (fn xs => Ctx.snoc xs x (a, EXP)) H'

      val (goalB, _, H') =
        makeGoal @@
          Hx >> TYPE (bx, EXP)

      val psi = T.empty @> goalA @> goalB
    in
      (psi, fn rho =>
        let
          val l1 = T.lookup rho (#1 goalA) // ([],[])
          val l2 = T.lookup rho (#1 goalB) // ([],[])
          (* is this necessary?: *)
          val _ = if VarCtx.member (varctx l2) x then raise Fail "Variable free in level expr" else ()
        in
          abtToAbs @@ Syn.into @@ Syn.LSUP (l1, l2)
        end)
    end
    | IsType _ _ _ = raise Match

  fun TypeEq destruct alpha (H >> EQ_MEM (quant1, quant2, univ)) =
    let
      val Syn.UNIV _ = Syn.out univ
      val (a1, x, b1x) = destruct quant1
      val (a2, y, b2y) = destruct quant2

      val (goal1, _, H) =
        makeGoal @@
          makeEqSequent H (a1,a2,univ)

      val z = alpha 0
      val ztm = check (`z, RS.EXP SortData.EXP)
      val b1z = subst (ztm, x) b1x
      val b2z = subst (ztm, y) b2y

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a1, SortData.EXP)) H

      val (goal2, _, H') =
        makeGoal @@
          ([], [(z, SortData.EXP)]) |> makeEqSequent H' (b1z, b2z, univ)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ _ = raise Match
end
