structure PiRules : PI_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 1 $ $$ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun destDFun m =
    case Syn.out m of
       Syn.DFUN (a, x, bx) => (a, x, bx)
     | _ => raise Match

  val IsType = QuantifierKit.IsType destDFun
  val TypeEq = QuantifierKit.TypeEq destDFun

  fun MemberEq alpha (H >> EQ_MEM (lam1, lam2, dfun)) =
    let
      val Syn.DFUN (a, x, bx) = Syn.out dfun
      val Syn.LAM (y1, m1) = Syn.out lam1
      val Syn.LAM (y2, m2) = Syn.out lam2

      val z = alpha 0
      val ztm = check (`z, RS.EXP EXP)

      val bz = subst (ztm, x) bx
      val m1z = subst (ztm, y1) m1
      val m2z = subst (ztm, y2) m2

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, EXP)) H

      val (goal1, _, H') =
        makeGoal @@
          [(z,EXP)] |> makeEqSequent H' (m1z, m2z, bz)

      val (goal2, _, _) =
        makeGoal @@
          H >> TYPE (a, EXP)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  fun ApSynth alpha (H >> SYN ap) =
    let
      val Syn.AP (r, m) = Syn.out ap

      val (tyGoal, tyHole, H') =
        makeGoal @@
          H >> SYN r

      val dom = Syn.into @@ Syn.DFUN_DOM @@ tyHole [] []

      val (chkGoal, _, _) =
        makeGoal @@
          H >> MEM (m, dom)

      val psi = T.empty @> tyGoal @> chkGoal
    in
      (psi, fn rho =>
        let
          val ty = T.lookup rho (#1 tyGoal) // ([],[])
        in
          abtToAbs @@ Syn.into @@ Syn.DFUN_COD (ty, r)
        end)
    end
    | ApSynth _ _ = raise Match

  fun Intro alpha (H >> TRUE (P, _)) =
    let
      val (a, x, bx) = destDFun P

      val z = alpha 0
      val ztm = check (`z, RS.EXP EXP)
      val bz = subst (ztm, x) bx

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, EXP)) H

      val (goal, _, _) =
        makeGoal @@
          [(z,EXP)] |> H' >> TRUE (bz, EXP)

      val (wfGoal, _, _) =
        makeGoal @@
          H >> TYPE (a, EXP)

      val psi = T.empty @> goal @> wfGoal
    in
      (psi, fn rho =>
        let
          val (_, [x]) \ mx = outb @@ T.lookup rho (#1 goal)
        in
          abtToAbs @@ Syn.into @@ Syn.LAM (x, mx)
        end)
    end
    | Intro _ _ = raise Match

  fun Elim f alpha (H >> TRUE (P, tau)) =
    let
      val (dfun, _) = Ctx.lookup (getHyps H) f
      val (a, x, bx) = destDFun dfun

      val y = alpha 0
      val z = alpha 1
      val ytm = check (`y, RS.EXP EXP)

      val (goal1, s, H) =
        makeGoal @@
          H >> TRUE (a, EXP)

      val bs = subst (s [] [], x) bx
      val ftm = check (`f, RS.EXP EXP)
      val fs = Syn.into @@ Syn.AP (ftm, s [] [])
      val yeqfs = Syn.into @@ Syn.EQ (EXP, ytm, fs, bs)

      val hctx = Ctx.snoc (Ctx.snoc Ctx.empty y (bs, EXP)) z (yeqfs, EXP)

      val H' = updateHyps (fn xs => Ctx.interposeAfter xs (f, hctx)) H

      val (goal2, _, _) =
        makeGoal @@
          [(y,EXP), (z, EXP)] |> H' >> TRUE (P, tau)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        let
          val s = T.lookup rho (#1 goal1) // ([],[])
          val fs = Syn.into @@ Syn.AP (ftm, s)
        in
          abtToAbs @@
            T.lookup rho (#1 goal2) // ([], [fs, Syn.into Syn.AX])
        end)
    end
    | Elim _ _ _ = raise Match

  fun Ext alpha (jdg as H >> EQ_MEM (f, g, dfun)) =
    let
      val (a, x, bx) = destDFun dfun

      val z = alpha 0
      val ztm = check (`z, RS.EXP EXP)
      val bz = subst (ztm, x) bx
      val fz = Syn.into @@ Syn.AP (f, ztm)
      val gz = Syn.into @@ Syn.AP (g, ztm)

      val H' = updateHyps (fn xs => Ctx.snoc xs z (a, EXP)) H

      val (mainGoal, _, H') =
        makeGoal @@
          [(z,EXP)] |> makeEqSequent H' (fz, gz, bz)

      val (fwfGoal, _, H) =
        makeGoal @@
          makeMemberSequent H (f, dfun)

      val (gwfGoal, _, _) =
        makeGoal @@
          makeMemberSequent H (g, dfun)

      val psi = T.empty @> mainGoal @> fwfGoal @> gwfGoal
    in
      (psi, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | Ext _ _ = raise Match

end
