structure AtomRules : ATOM_RULES =
struct
  open RefinerKit OperatorData CttOperatorData AtomsOperatorData LevelOperatorData SortData
  infix @@ $ $# \ @>
  infix 4 >>
  infix 3 |>

  fun destAtom m =
    case out m of
         ATM (ATOM tau) $ [] => tau
       | _ =>
           raise Fail
             @@ "Expected Atom but got "
              ^ DebugShowAbt.toString m

  fun makeAtom tau =
    check' (ATM (ATOM tau) $ [], EXP)

  fun destToken m =
    case out m of
         ATM (TOKEN (u,tau)) $ [] => (u,tau)
       | _ =>
           raise Fail
             @@ "Expected Token but got "
              ^ DebugShowAbt.toString m

  fun destTest m =
    case out m of
         ATM (TEST (sigma, tau)) $ [_ \ t1, _ \ t2, _ \ yes, _ \ no] =>
           (sigma, tau, t1, t2, yes, no)
       | _ =>
           raise Fail
             @@ "Expected Test but got "
              ^ DebugShowAbt.toString m

  fun IsType _ (H >> TYPE (atm, EXP)) =
    let
      val _ = destAtom atm
    in
      (T.empty, fn rho =>
        abtToAbs @@
          check' (LVL_OP LBASE $ [], LVL))
    end
    | IsType _ _ = raise Match

  fun TypeEq _ (H >> EQ_MEM (atm1, atm2, univ)) =
    let
      val (sigma, lvl) = destUniv univ
      val tau1 = destAtom atm1
      val tau2 = destAtom atm2
      val _ = if sigma = EXP andalso tau1 = tau2 then () else raise Match
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq _ (H >> EQ_MEM (tok1, tok2, atm)) =
    let
      val tau = destAtom atm
      val (u1,tau1) = destToken tok1
      val (u2,tau2) = destToken tok2
      val _ =
        if Symbol.eq (u1,u2) andalso tau1 = tau2 andalso tau = tau1 then
          ()
        else
          raise Match
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | MemberEq _ _ = raise Match

  fun TestEq alpha (H >> EQ_MEM (test1, test2, a)) =
    let
      val (sigma, tau, t1, t2, yes, no) = destTest test1
      val (sigma', tau', t1', t2', yes', no') = destTest test2

      val _ = if sigma = sigma' andalso tau = tau' then () else raise Match

      val (goal1, _, H) =
        makeGoal @@
          makeEqSequent H (t1, t1', makeAtom sigma)

      val (goal2, _, H) =
        makeGoal @@
          makeEqSequent H (t2, t2', makeAtom sigma)

      val z = alpha 0

      val atomTy = makeAtom sigma
      val toksEq = makeEq (getMetas H) (t1, t2, atomTy)
      val toksNotEq = check (getMetas H) (CTT NOT $ [([],[]) \ toksEq], EXP)

      val Hyes = updateHyps (fn xs => Ctx.snoc xs z (toksEq, EXP)) H
      val Hno = updateHyps (fn xs => Ctx.snoc xs z (toksNotEq, EXP)) H

      val (goalYes, _, _) =
        makeGoal @@
          [(z, EXP)] |> makeEqSequent Hyes (yes, yes', a)

      val (goalNo, _, _) =
        makeGoal @@
          [(z, EXP)] |> makeEqSequent Hno (no, no', a)

      val psi = T.empty @> goal1 @> goal2 @> goalYes @> goalNo
    in
      (psi, fn rho =>
        abtToAbs makeAx)
    end
    | TestEq _ _ = raise Match
end
