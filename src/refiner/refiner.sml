structure Refiner : REFINER =
struct
  structure Abt = Abt
  open RefinerKit

  open Sequent infix >> $ \

  fun Elim i _ =
    raise Fail "To be implemented"

  fun Intro r _ =
    raise Fail "To be implemented"

  local
    open OperatorData CttOperatorData Tacticals
    infix ORELSE
  in
    fun Eq r alpha (jdg as H >> (P, _)) =
      case out P of
           CTT (EQ _) $ _ =>
             (UnivRules.Eq alpha
               ORELSE BaseRules.TypeEq alpha
               ORELSE BaseRules.MemberEq alpha
               ORELSE SquashRules.TypeEq alpha
               ORELSE SpeciesRules.TypeEq alpha
               ORELSE SpeciesRules.MemberEq alpha) jdg
         | _ => raise Fail "Eq not applicable"
  end

  fun Witness m alpha (H >> (P, _)) =
    let
      val goal =
        (newMeta "",
         makeMemberSequent H (m, P))
      val psi = T.snoc T.empty goal
    in
      (psi, fn rho =>
        abtToAbs m)
    end

  fun Hyp i _ (H >> (P, _)) =
    let
      val (Q, tau) = Ctx.lookup (#hypctx H) i
    in
      if Abt.eq (P, Q) then
        (T.empty, fn rho =>
          abtToAbs (check' (`i , tau)))
      else
        raise Fail "Failed to unify with hypothesis"
    end

  val Unhide =
    SquashRules.Unhide

  local
    open OperatorData CttOperatorData SortData
    fun destCEquiv P =
      case (out P) of
           CTT (CEQUIV tau) $ [_ \ m, _ \ n] =>
             let
               val tau1 = sort m
               val tau2 = sort n
               val () =
                 if tau1 = tau2 andalso tau = tau1 then
                   ()
                 else
                   raise Fail "Incompatible sorts in CEquiv"
             in
               (tau, m, n)
             end
         | _ => raise Fail "Expected CEquiv"
    val ax = check' (CTT AX $ [], TRIV)
  in
    fun CSym _ (H >> (P, _)) =
      let
        val (tau, m, n) = destCEquiv P
        val x = newMeta ""
        val subgoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ n, ([],[]) \ m], EXP)
        val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
      in
        (psi, fn rho =>
          abtToAbs ax)
      end

    fun CStep sign i _ (H >> (P, _)) =
      let
        val (tau, m, n) = destCEquiv P
        val m' = DynamicsUtil.stepn sign i m
      in
        (if Abt.eq (m', n) then
          (T.empty, fn rho =>
            abtToAbs ax)
         else
           let
             val x = newMeta ""
             val subgoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ m', ([],[]) \ n], EXP)
             val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
           in
             (psi, fn rho =>
               abtToAbs ax)
           end)
      end

    fun CEval sign _ (H >> (P, _)) =
      let
        val (tau, m, n) = destCEquiv P
        val m' = DynamicsUtil.evalOpen sign m
      in
        (if Abt.eq (m', n) then
          (T.empty, fn rho =>
            abtToAbs ax)
         else
           let
             val x = newMeta ""
             val subgoal = check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ m', ([],[]) \ n], EXP)
             val psi = T.snoc T.empty (x, H >> (subgoal, TRIV))
           in
             (psi, fn rho =>
               abtToAbs ax)
           end)
      end


    fun RewriteGoal Q _ (H >> (P, sigma)) =
      let
        val tau = sort P
        val ceqGoal =
          (newMeta "",
           H >> (check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ P, ([],[]) \ Q], EXP), EXP))
        val mainGoal = (newMeta "", H >> (Q, sigma))
        val psi = T.snoc (T.snoc T.empty ceqGoal) mainGoal
      in
        (psi, fn rho => T.lookup rho (#1 mainGoal))
      end

    fun EvalGoal sign _ (H >> (P, sigma)) =
      let
        val Q = DynamicsUtil.evalOpen sign P
        val x = newMeta ""
        val psi = T.snoc T.empty (x, H >> (Q, sigma))
      in
        (psi, fn rho =>
           T.lookup rho x)
      end

  end

end
