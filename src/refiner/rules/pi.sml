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

      val lvlGoal =
        (newMeta "",
         [] |> makeLevelSequent H)

      val H' =
        {metactx = MetaCtx.insert (#metactx H) (#1 lvlGoal) (([],[]), LVL),
         symctx = #symctx H,
         hypctx = #hypctx H}

      val lvlHole =
        check
          (#metactx H')
          (#1 lvlGoal $# ([], []),
           LVL)

      val domGoal =
        (newMeta "",
         [] |> H' >> TRUE (makeUniv lvlHole, EXP))

      val mctx = MetaCtx.insert (#metactx H') (#1 domGoal) (([],[]), EXP)

      val domHole =
        check
          mctx
          (#1 domGoal $# ([],[]),
           EXP)

      val z = alpha 0

      val H'' =
        {metactx = mctx,
         symctx = #symctx H',
         hypctx = Ctx.snoc (#hypctx H') z (domHole, EXP)}

      val codGoal =
        (newMeta "",
         [(z,EXP)] |> H'' >> TRUE (makeUniv lvlHole, EXP))

      val mctx' = MetaCtx.insert mctx (#1 codGoal) (([],[]), EXP)

      val codHole =
        check
          mctx'
          (#1 codGoal $# ([],[]),
           EXP)

      val dfun =
        check
          mctx'
          (CTT DFUN $ [([],[]) \ domHole, ([],[z]) \ codHole],
           EXP)

      val H''' =
        {metactx = mctx',
         symctx = #symctx H,
         hypctx = #hypctx H}

      val ceqGoal =
        (newMeta "",
         [] |> H''' >> TRUE (makeCEquiv mctx' (c, subst (n1, z) codHole), EXP))

      val goal1 =
        (newMeta "",
         [] |> makeEqSequent H''' (m1, m2, dfun))

      val goal2 =
        (newMeta "",
         [] |> makeEqSequent H''' (n1, n2, domHole))

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

      val goal =
        (newMeta "",
         [(z,EXP)] |> H' >> TRUE (bz, EXP))

      val wfGoal =
        (newMeta "",
         [] |> H >> TYPE (a, EXP))

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

  fun Elim i alpha (G |> H >> TRUE (P, _)) =
    let
    in
      ?hole
    end
    | Elim _ _ _ = raise Match

end
