structure RecordRules : RECORD_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ $# \ @>
  infix 2 //
  infix 3 >>
  infix 2 |>

  fun IsType alpha (goal as (H >> TYPE (ty, EXP))) =
    let
      val Syn.RCD_SINGL (lbl, a) = Syn.out ty

      val (goalA, holeA, H') =
        makeGoal @@
          H >> TYPE (a, EXP)

      val psi = T.empty @> goalA
    in
      (psi, fn rho =>
          T.lookup rho (#1 goalA))
    end
    | IsType _ _ = raise Match

  fun TypeEq alpha (H >> EQ_MEM (ty1, ty2, univ)) =
    let
      val Syn.UNIV (tau, lvl) = Syn.out univ
      val _ = if tau = EXP then () else raise Match

      val Syn.RCD_SINGL (lbl1, a1) = Syn.out ty1
      val Syn.RCD_SINGL (lbl2, a2) = Syn.out ty2
      val _ = if Symbol.eq (lbl1, lbl2) then () else raise Match

      val (goal, _, _) =
        makeGoal @@
          makeEqSequent H (a1, a2, Syn.into @@ Syn.UNIV (EXP, lvl))

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> EQ_MEM (rcd1, rcd2, ty)) =
    let
      val Syn.RCD_SINGL (lbl, a) = Syn.out ty

      val proj1 = Syn.into @@ Syn.RCD_PROJ (lbl, rcd1)
      val proj2 = Syn.into @@ Syn.RCD_PROJ (lbl, rcd2)

      val (goal, _, _) =
        makeGoal @@
          makeEqSequent H (proj1, proj2, a)

      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  (* H >> R.lbl synth ~> A
   *   H >> R synth ~> singl[lbl](A)
   *)
  fun ProjSynth alpha (H >> SYN p) =
    let
      val Syn.RCD_PROJ (lbl, rcd) = Syn.out p

      val (tyGoal, tyHole, H') =
        makeGoal @@
          H >> SYN rcd

      val psi = T.empty @> tyGoal
    in
      (psi, fn rho =>
        let
          val ty = T.lookup rho (#1 tyGoal) // ([],[])
        in
          abtToAbs @@ Syn.into @@ Syn.SINGL_GET_TY ty
        end)
    end
    | ProjSynth _ _ = raise Match
end
