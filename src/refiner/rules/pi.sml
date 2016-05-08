structure PiRules : PI_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  val destDFun =
    QuantifierKit.destQuantifier (CTT DFUN)

  fun destLam m =
    case out m of
         CTT LAM $ [(_, [x]) \ m] => (x, m)
       | _ =>
           raise Fail
             @@ "Expected Lam but got "
              ^ DebugShowAbt.toString m

  fun destAp m =
    case out m of
         CTT AP $ [_ \ m, _ \ n] => (m, n)
       | _ =>
           raise Fail
             @@ "Expected Ap but got "
              ^ DebugShowAbt.toString m

  fun makeAp mctx m n =
    check
      mctx
      (CTT AP $ [([],[]) \ m, ([],[]) \ n], EXP)


  val IsType = QuantifierKit.IsType (CTT DFUN)
  val TypeEq = QuantifierKit.TypeEq (CTT DFUN)

  fun MemberEq alpha (H >> EQ_MEM (lam1, lam2, dfun)) =
    let
      val (a, x, bx) = destDFun dfun
      val (y1, m1) = destLam lam1
      val (y2, m2) = destLam lam2

      val z = alpha 0
      val ztm = check' (`z, EXP)

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
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  fun ApSynth alpha (H >> SYN ap) =
    let
      val (r, m) = destAp ap

      val (tyGoal, tyHole, H') =
        makeGoal @@
          H >> SYN r

      val dom =
        check
          (getMetas H)
          (CTT DFUN_DOM $ [([],[]) \ tyHole [] []], EXP)

      val (chkGoal, _, _) =
        makeGoal @@
          H >> MEM (m, dom)

      val psi = T.empty @> tyGoal @> chkGoal
    in
      (psi, fn rho =>
        let
          val ty = T.lookup rho (#1 tyGoal) // ([],[])
        in
          abtToAbs @@
            check
              (getMetas H)
              (CTT DFUN_COD $ [([],[]) \ ty, ([],[]) \ r], EXP)
        end)
    end
    | ApSynth _ _ = raise Match

  fun Intro alpha (H >> TRUE (P, _)) =
    let
      val (a, x, bx) = destDFun P

      val z = alpha 0
      val ztm = check' (`z, EXP)
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
          val ev = outb @@ T.lookup rho (#1 goal)
        in
          abtToAbs @@
            check
              (getMetas H)
              (CTT LAM $ [ev], EXP)
        end)
    end
    | Intro _ _ = raise Match

  fun Elim f alpha (H >> TRUE (P, tau)) =
    let
      val (dfun, _) = Ctx.lookup (getHyps H) f
      val (a, x, bx) = destDFun dfun

      val y = alpha 0
      val z = alpha 1
      val ytm = check' (`y, EXP)

      val (goal1, s, H) =
        makeGoal @@
          H >> TRUE (a, EXP)

      val bs = subst (s [] [], x) bx
      val ftm = check' (`f, EXP)
      val fs = makeAp (getMetas H) ftm (s [] [])
      val yeqfs = makeEq (getMetas H) (ytm, fs, bs)

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
          val fs = makeAp (metactx s) ftm s
        in
          abtToAbs @@
            T.lookup rho (#1 goal2) // ([], [fs, makeAx])
        end)
    end
    | Elim _ _ _ = raise Match

  fun Ext alpha (jdg as H >> EQ_MEM (f, g, dfun)) =
    let
      val (a, x, bx) = destDFun dfun

      val z = alpha 0
      val ztm = check' (`z, EXP)
      val bz = subst (ztm, x) bx
      val fz = makeAp (getMetas H) f ztm
      val gz = makeAp (getMetas H) g ztm

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
        abtToAbs makeAx)
    end
    | Ext _ _ = raise Match

end
