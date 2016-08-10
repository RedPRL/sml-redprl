structure RecordRules : RECORD_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ $# \ @> <@
  infix 2 //
  infix 3 >>
  infix 2 |>

  val IsType =
    QuantifierKit.IsType (fn ty =>
      let
        val Syn.RECORD_TY (lbl, a, x, bx) = Syn.out ty
      in
        (a, x, bx)
      end)

  fun TypeEq alpha (H >> EQ_MEM (rcd1, rcd2, univ)) =
    let
      val Syn.UNIV _ = Syn.out univ
      val Syn.RECORD_TY (lbl1, a1, x, b1x) = Syn.out rcd1
      val Syn.RECORD_TY (lbl2, a2, y, b2y) = Syn.out rcd2

      val _ = if Symbol.eq (lbl1, lbl2) then () else raise Match

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
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (rcd1, rcd2, ty)) =
    let
      val Syn.RECORD_TY (lbl, a, x, bx) = Syn.out ty
      val proj1 = Syn.into @@ Syn.RCD_PROJ (lbl, rcd1)
      val proj2 = Syn.into @@ Syn.RCD_PROJ (lbl, rcd2)

      val (goal1, _, _) =
        makeGoal @@
          makeEqSequent H (proj1, proj2, a)

      val (goal2, _, _) =
        makeGoal @@
          makeEqSequent H (rcd1, rcd2, subst (proj1, x) bx)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
         abtToAbs @@ Syn.into Syn.AX)
    end
  | MemberEq _ _ = raise Match

  fun Intro alpha (H >> TRUE (ty, EXP)) =
    let
      val Syn.RECORD_TY (lbl, a, x, bx) = Syn.out ty
      val (goalA, holeA, H') = makeGoal @@ H >> TRUE (a, EXP)
      val b' = subst (holeA [] [], x) bx

      val (goalB, _, _) = makeGoal @@ H' >> TRUE (b', EXP)
      val psi = T.empty @> goalA @> goalB
    in
      (psi, fn rho =>
         let
           val hd = T.lookup rho (#1 goalA) // ([],[])
           val tl = T.lookup rho (#1 goalB) // ([],[])
         in
           abtToAbs @@ Syn.into @@ Syn.RCD_CONS (lbl, hd, tl)
         end)
    end
    | Intro _ _ = raise Match

  fun ProjSynth alpha (H >> SYN proj) =
    let
      val Syn.RCD_PROJ (lbl, rcd) = Syn.out proj
      val (tyGoal, tyHole, H') = makeGoal @@ H >> SYN rcd
      val psi = T.empty @> tyGoal
    in
      (psi, fn rho =>
        let
          val ty = T.lookup rho (#1 tyGoal) // ([],[])
        in
          abtToAbs @@ Syn.into @@ Syn.RCD_PROJ_TY (lbl, ty, rcd)
        end)
    end
    | ProjSynth _ _ = raise Match
end
