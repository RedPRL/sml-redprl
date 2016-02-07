structure Refiner : REFINER =
struct
  structure Abt = Abt
  open RefinerKit

  open Sequent infix >> $ \

  fun Elim i _ =
    raise Fail "To be implemented"

  fun Intro r alpha =
    SquashRules.Intro alpha

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
               ORELSE CEquivRules.TypeEq alpha
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

  open CEquivRules

  local
    open CEquivRules
  in
    val CStep = CStep
    val CEval = CEval
    val CSym = CSym
  end

  local
    open OperatorData CttOperatorData SortData
  in

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
