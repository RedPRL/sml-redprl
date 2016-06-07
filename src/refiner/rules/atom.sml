structure AtomRules : ATOM_RULES =
struct
  open RefinerKit SortData
  infixr 0 @@
  infix 2 $ $$ $# \ @>
  infix 4 >>
  infix 3 |>

  fun IsType _ (H >> TYPE (atm, EXP)) =
    let
      val Syn.ATOM _ = Syn.out atm
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.LBASE)
    end
    | IsType _ _ = raise Match

  fun TypeEq _ (H >> EQ_MEM (atm1, atm2, univ)) =
    let
      val Syn.UNIV (sigma, lvl) = Syn.out univ
      val Syn.ATOM tau1 = Syn.out atm1
      val Syn.ATOM tau2 = Syn.out atm2
      val _ = if sigma = EXP andalso tau1 = tau2 then () else raise Match
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TypeEq _ _ = raise Match

  fun MemberEq _ (H >> EQ_MEM (tok1, tok2, atm)) =
    let
      val Syn.ATOM tau = Syn.out atm
      val Syn.TOKEN (u1,tau1) = Syn.out tok1
      val Syn.TOKEN (u2,tau2) = Syn.out tok2
      val _ =
        if Symbol.eq (u1,u2) andalso tau1 = tau2 andalso tau = tau1 then
          ()
        else
          raise Match
    in
      (T.empty, fn rho =>
        abtToAbs @@ Syn.into Syn.AX)
    end
    | MemberEq _ _ = raise Match

  fun TestEq alpha (H >> EQ_MEM (test1, test2, a)) =
    let
      val Syn.IF_EQ (sigma, tau, t1, t2, yes, no) = Syn.out test1
      val Syn.IF_EQ (sigma', tau', t1', t2', yes', no') = Syn.out test2

      val _ = if sigma = sigma' andalso tau = tau' then () else raise Match

      val atomTy = Syn.into @@ Syn.ATOM sigma

      val (goal1, _, H) =
        makeGoal @@
          makeEqSequent H (t1, t1', atomTy)

      val (goal2, _, H) =
        makeGoal @@
          makeEqSequent H (t2, t2', atomTy)

      val z = alpha 0

      val toksEq = Syn.into @@ Syn.EQ (EXP, t1, t2, atomTy)
      val toksNotEq = Syn.into @@ Syn.NOT toksEq

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
        abtToAbs @@ Syn.into Syn.AX)
    end
    | TestEq _ _ = raise Match
end
