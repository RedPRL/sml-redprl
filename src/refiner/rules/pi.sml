structure PiRules : PI_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ $ $# \ @>
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

  fun TypeEq alpha (G |> H >> TRUE (P, _)) =
    let
      val (_, dfun1, dfun2, univ) = destEq P
      val _ = destUniv univ
      val (a1, x, b1x) = destDFun dfun1
      val (a2, y, b2y) = destDFun dfun2

      val goal1 =
        (newMeta "",
         [] |> makeEqSequent H (a1,a2,univ))

      val z = alpha 0
      val ztm = check' (`z, EXP)
      val b1z = subst (ztm, x) b1x
      val b2z = subst (ztm, y) b2y

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) z (a1, EXP)}

      val goal2 =
        (newMeta "",
         [(z,EXP)] |> makeEqSequent H' (b1z, b2z, univ))

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        makeEvidence G H makeAx)
    end
    | TypeEq _ _ = raise Match

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

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) z (a, EXP)}

      val goal1 =
        (newMeta "",
         [(z,EXP)] |> makeEqSequent H' (m1z, m2z, bz))

      val goal2 =
        (newMeta "",
         [] |> H >> TYPE (a, EXP))

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

      val (lvlGoal, lvlHole, mctx) =
        makeGoal @@
          [] |> makeLevelSequent H

      val H' =
        {metactx = mctx,
         symctx = #symctx H,
         hypctx = #hypctx H}

      val univ = makeUniv @@ lvlHole [] []

      val (domGoal, domHole, mctx') =
        makeGoal @@
          [] |> H' >> TRUE (univ, EXP)

      val z = alpha 0
      val ztm = check' (`z, EXP)

      val H'' =
        {metactx = mctx',
         symctx = #symctx H',
         hypctx = Ctx.snoc (#hypctx H') z (domHole [] [], EXP)}

      val codGoal =
        (newMeta "",
         [(z,EXP)] |> H'' >> TRUE (univ, EXP))

      val mctx'' = MetaCtx.insert mctx' (#1 codGoal) (([],[EXP]), EXP)

      val codHole =
        check
          mctx''
          (#1 codGoal $# ([],[ztm]),
           EXP)

      val dfun =
        check
          mctx''
          (CTT DFUN $ [([],[]) \ domHole [] [], ([],[z]) \ codHole],
           EXP)

      val H''' =
        {metactx = mctx'',
         symctx = #symctx H,
         hypctx = #hypctx H}

      val (ceqGoal, _, _) =
        makeGoal @@
          [] |> H''' >> TRUE (makeCEquiv mctx' (c, subst (n1, z) codHole), EXP)

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

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) z (a, EXP)}

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
              (#metactx H)
              (CTT LAM $ [ev], EXP)
        end)
    end
    | Intro _ _ = raise Match

  fun Elim f alpha (G |> H >> TRUE (P, tau)) =
    let
      val (dfun, _) = Ctx.lookup (#hypctx H) f
      val (a, x, bx) = destDFun dfun

      val y = alpha 0
      val z = alpha 1
      val ytm = check' (`y, EXP)

      val (goal1, s, mctx) =
        makeGoal @@
          [] |> H >> TRUE (a, EXP)

      val bs = subst (s [] [], x) bx
      val ftm = check' (`f, EXP)
      val fs = check mctx (CTT AP $ [([],[]) \ ftm, ([],[]) \ s [] []], EXP)
      val yeqfs = makeEq mctx (ytm, fs, bs)

      val hctx = Ctx.snoc (Ctx.snoc Ctx.empty y (bs, EXP)) z (yeqfs, EXP)

      val H' =
        {metactx = mctx,
         symctx = #symctx H,
         hypctx = Ctx.interposeAfter (#hypctx H) (f, hctx)}

      val (goal2, _, _) =
        makeGoal @@
          [(y,EXP), (z, EXP)] |> H' >> TRUE (P, tau)

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        let
          val sb = T.lookup rho (#1 goal1)
          val tb = T.lookup rho (#1 goal2)
        in
          case (outb sb, outb tb) of
               (_ \ s, (_, [x,y]) \ t) =>
                 let
                   val fs = check (metactx s) (CTT AP $ [([],[]) \ ftm, ([],[]) \ s], EXP)
                   val env = VarCtx.insert (VarCtx.insert VarCtx.empty x fs) y makeAx
                 in
                   makeEvidence G H @@
                     substEnv env t
                 end
             | _ => raise Match
        end)
    end
    | Elim _ _ _ = raise Match

end
