structure PiRules : PI_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ >> $ $# \ @>

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

  fun TypeEq alpha (H >> TRUE (P, _)) =
    let
      val (_, dfun1, dfun2, univ) = destEq P
      val _ = destUniv univ
      val (a1, x, b1x) = destDFun dfun1
      val (a2, y, b2y) = destDFun dfun2

      val goal1 =
        (newMeta "",
         makeEqSequent H (a1,a2,univ))

      val z = alpha 0
      val ztm = check' (`z, EXP)
      val b1z = subst (ztm, x) b1x
      val b2z = subst (ztm, y) b2y

      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) (z, (a1, EXP))}

      val goal2 =
        (newMeta "",
         makeEqSequent H' (b1z, b2z, univ))

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq alpha (H >> TRUE (P, _)) =
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
         hypctx = Ctx.snoc (#hypctx H) (z, (a, EXP))}

      val goal1 =
        (newMeta "",
         makeEqSequent H' (m1z, m2z, bz))

      val goal2 =
        (newMeta "",
         H >> TYPE (a, EXP))

      val psi = T.empty @> goal1 @> goal2
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  fun ElimEq alpha (H >> TRUE (P, _)) =
    let
      val (_, ap1, ap2, c) = destEq P
      val (m1, n1) = destAp ap1
      val (m2, n2) = destAp ap2
    in
      ?hole
    end
    | ElimEq _ _ = raise Match

end
