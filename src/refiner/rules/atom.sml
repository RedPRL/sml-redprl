structure AtomRules =
struct
  open RefinerKit OperatorData CttOperatorData AtomsOperatorData SortData
  infix @@ >> $ $# \ @>

  fun destAtom m =
    case out m of
         ATM (ATOM tau) $ [] => tau
       | _ =>
           raise Fail
             @@ "Expected Atom but got "
              ^ DebugShowAbt.toString m

  fun destToken m =
    case out m of
         ATM (TOKEN (u,tau)) $ [] => (u,tau)
       | _ =>
           raise Fail
             @@ "Expected Token but got "
              ^ DebugShowAbt.toString m

  fun TypeEq _ (H >> TRUE (P, _)) =
    let
      val (_, atm1, atm2, univ) = destEq P
      val (sigma, lvl) = destUniv univ
      val tau1 = destAtom atm1
      val tau2 = destAtom atm2
      val _ = if sigma = EXP andalso tau1 = tau2 then () else raise Match
    in
      (T.empty, fn rho =>
        abtToAbs makeAx)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq _ (H >> TRUE (P, _)) =
    let
      val (_,tok1,tok2,atm) = destEq P
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
end
