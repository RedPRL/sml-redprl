structure Refiner : REFINER =
struct
  structure Abt = Abt
  open RefinerKit

  open Sequent infix >> $ \ @@

  structure HoleUtil = HoleUtil (structure Tm = Abt and J = Judgment and T = T)

  fun stateToString (psi, vld) =
    let
      open T.ConsView
      fun go i =
        fn Empty => (T.empty, "")
         | Cons (x, jdg, tl) =>
             let
               val var = Metavariable.named ("?" ^ Int.toString i)
               val goal = "\nHOLE " ^ Metavariable.toString var ^ "\n--------------------------------------------\n" ^ Judgment.judgmentToString jdg
               val vartm = HoleUtil.makeHole (var, Judgment.evidenceValence jdg)
               val tl' = Telescope.map tl @@ Judgment.substJudgment (x, vartm)
               val (rho, rest) = go (i + 1) (out tl')
             in
               (T.snoc rho (x, vartm), goal ^ "\n" ^ rest)
             end

      val (env, subgoals) = go 0 @@ out psi
      val preamble = Judgment.evidenceToString (vld env)
    in
      "WITNESS:\n============================================\n\n" ^ preamble ^ "\n\n" ^ subgoals
    end


  local
    open OperatorData CttOperatorData Tacticals
    infix ORELSE
  in
    fun Elim i alpha =
      BaseRules.Elim i alpha
        ORELSE EnsembleRules.Elim i alpha
        ORELSE VoidRules.Elim i alpha

    fun Intro r alpha =
      SquashRules.Intro alpha
        ORELSE EnsembleRules.Intro alpha
        ORELSE PiRules.Intro alpha
        ORELSE TypeRules.Intro alpha

    fun Eq r alpha (jdg as H >> TRUE (P, _)) =
      (case out P of
           CTT (EQ _) $ _ =>
             (UnivRules.Eq alpha
               ORELSE BaseRules.TypeEq alpha
               ORELSE BaseRules.MemberEq alpha
               ORELSE CEquivRules.TypeEq alpha
               ORELSE SquashRules.TypeEq alpha
               ORELSE EnsembleRules.TypeEq alpha
               ORELSE EnsembleRules.MemberEq alpha
               ORELSE AtomRules.TypeEq alpha
               ORELSE AtomRules.MemberEq alpha
               ORELSE AtomRules.TestEq alpha
               ORELSE PiRules.TypeEq alpha
               ORELSE PiRules.MemberEq alpha
               ORELSE PiRules.ElimEq alpha
               ORELSE VoidRules.TypeEq alpha) jdg
         | _ => raise Fail "Eq not applicable")
      | Eq _ _ _ = raise Match
  end

  fun Witness m alpha (H >> TRUE (P, _)) =
    let
      val goal =
        (newMeta "",
         makeMemberSequent H (m, P))
      val psi = T.snoc T.empty goal
    in
      (psi, fn rho =>
        abtToAbs m)
    end
    | Witness _ _ _ = raise Match

  fun Hyp i _ (H >> TRUE (P, _)) =
    let
      val (Q, tau) = Ctx.lookup (#hypctx H) i
    in
      if Abt.eq (P, Q) then
        (T.empty, fn rho =>
          abtToAbs (check' (`i , tau)))
      else
        raise Fail "Failed to unify with hypothesis"
    end
    | Hyp _ _ _ = raise Match

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
    open OperatorData CttOperatorData AtomsOperatorData SortData
  in

    fun RewriteGoal Q _ (H >> TRUE (P, sigma)) =
      let
        val tau = sort P
        val ceqGoal =
          (newMeta "",
           H >> TRUE (check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ P, ([],[]) \ Q], EXP), EXP))
        val mainGoal = (newMeta "", H >> TRUE (Q, sigma))
        val psi = T.snoc (T.snoc T.empty ceqGoal) mainGoal
      in
        (psi, fn rho => T.lookup rho (#1 mainGoal))
      end
      | RewriteGoal _ _ _ = raise Match

    fun EvalGoal sign _ (H >> TRUE (P, sigma)) =
      let
        val Q = DynamicsUtil.evalOpen sign P
        val x = newMeta ""
        val psi = T.snoc T.empty (x, H >> TRUE (Q, sigma))
      in
        (psi, fn rho =>
           T.lookup rho x)
      end
      | EvalGoal _ _ _ = raise Match

    local
      open LevelOperatorData
      val lbase = check' (LVL_OP LBASE $ [], LVL)
    in
      fun inferTypeLevel (H : Sequent.context) P =
        case out P of
            CTT (UNIV _) $ [_ \ i] => check (#metactx H) (LVL_OP LSUCC $ [([],[]) \ i], LVL)
          | CTT (BASE _) $ _ => lbase
          | CTT (CEQUIV _) $ _ => lbase
          | CTT (CAPPROX _) $ _ => lbase
          | CTT (EQ _) $ _ => lbase
          | CTT (SQUASH _) $ [_ \ a] => inferTypeLevel H a (* we may be able to make this just [lbase] *)
          | ATM (ATOM _) $ _ => lbase
          | `x =>
              let
                val (univ, _) = Ctx.lookup (#hypctx H) x
                val (_, i) = destUniv univ
              in
                i
              end
          | _ => raise Fail "Level inference heuristic failed"
    end

    fun ProveIsType alpha =
      fn jdg as H >> TYPE (P, tau) =>
           Tacticals.THENF
             (TypeRules.Intro alpha, 0, Witness (inferTypeLevel H P) alpha)
             jdg
       | _ => raise Match
  end

  local
    open Tacticals
    infix 2 THEN ORELSE
  in
    fun AutoStep sign alpha : Lcf.tactic =
        TRY @@
          ProveIsType alpha
            ORELSE Intro NONE alpha
            ORELSE Eq NONE alpha
            ORELSE CStep sign 0 alpha
            ORELSE EvalGoal sign alpha
  end
end
