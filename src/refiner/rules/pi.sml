structure PiRules : PI_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ $# \ @>
  infix 2 //
  infix 4 >>
  infix 3 |>

  fun destDFun m =
    case out m of
         CTT DFUN $ [_ \ a, (_, [x]) \ b] => (a, x, b)
       | _ =>
           raise Fail
             @@ "Expected DFun but got "
              ^ DebugShowAbt.toString m

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


  val TypeEq = QuantifierKit.TypeEq (CTT DFUN)

  fun MemberEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_, lam1, lam2, dfun) = destEq P
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
          [] |> H >> TYPE (a, EXP)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | MemberEq _ _ = raise Match

  fun ElimEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_, ap1, ap2, c) = destEq P
      val (m1, n1) = destAp ap1
      val (m2, n2) = destAp ap2

      val (lvlGoal, lvlHole, H) =
        makeGoal @@
          [] |> makeLevelSequent H

      val univ = makeUniv @@ lvlHole [] []

      val (domGoal, domHole, H') =
        makeGoal @@
          [] |> H >> TRUE (univ, EXP)

      val z = alpha 0
      val ztm = check' (`z, EXP)

      val H'' = updateHyps (fn xs => Ctx.snoc xs z (domHole [] [], EXP)) H'

      val (codGoal, codHole, H'') =
        makeGoal @@
          [(z,EXP)] |> H'' >> TRUE (univ, EXP)

      val dfun =
        check
          (getMetas H'')
          (CTT DFUN $ [([],[]) \ domHole [] [], ([],[z]) \ codHole [] [ztm]],
           EXP)

      val H''' = updateMetas (fn _ => getMetas H'') H

      val (ceqGoal, _, _) =
        makeGoal @@
          [] |> H''' >> TRUE (makeCEquiv (getMetas H''') (c, codHole [] [n1]), EXP)

      val (goal1, _, _) =
        makeGoal @@
          [] |> makeEqSequent H''' (m1, m2, dfun)

      val (goal2, _, _) =
        makeGoal @@
          [] |> makeEqSequent H''' (n1, n2, domHole [] [])

      val psi =
        T.empty
          @> lvlGoal
          @> domGoal
          @> codGoal
          @> ceqGoal
          @> goal1
          @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | ElimEq _ _ = raise Match

  fun Intro alpha (G |> H >> TRUE (P, _)) =
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
          [] |> H >> TYPE (a, EXP)

      val psi = T.empty @> goal @> wfGoal
    in
      (psi, fn rho =>
        let
          val ev = outb @@ T.lookup rho (#1 goal)
        in
          makeEvidence G H @@
            check
              (getMetas H)
              (CTT LAM $ [ev], EXP)
        end)
    end
    | Intro _ _ = raise Match

  fun Elim f alpha (G |> H >> TRUE (P, tau)) =
    let
      val (dfun, _) = Ctx.lookup (getHyps H) f
      val (a, x, bx) = destDFun dfun

      val y = alpha 0
      val z = alpha 1
      val ytm = check' (`y, EXP)

      val (goal1, s, H) =
        makeGoal @@
          [] |> H >> TRUE (a, EXP)

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
          makeEvidence G H @@
            T.lookup rho (#1 goal2) // ([], [fs, makeAx])
        end)
    end
    | Elim _ _ _ = raise Match

  fun Ext alpha (jdg as G |> H >> TRUE (P, _)) =
    let
      val (_, f, g, dfun) = destEq P
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
          [] |> makeMemberSequent H (f, dfun)

      val (gwfGoal, _, _) =
        makeGoal @@
          [] |> makeMemberSequent H (g, dfun)

      val psi = T.empty @> mainGoal @> fwfGoal @> gwfGoal
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | Ext _ _ = raise Match

end
