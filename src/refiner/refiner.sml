structure Refiner : REFINER =
struct
  structure Abt = Abt
  open RefinerKit

  open Sequent
  infix $ \ @@ @> $#
  infix 2 //
  infix 4 >>
  infix 3 |>


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

    fun HypEq alpha (G |> H >> TRUE (P, _)) =
      let
        val (_, m, n, a) = destEq P
        val x = destVar m
        val y = destVar n
        val _ = if Variable.eq (x, y) then () else raise Match
        val (a', _) = Ctx.lookup (getHyps H) x
        val _ = if Abt.eq (a,a') then () else raise Match
      in
        (T.empty, fn rho =>
          makeEvidence G H makeAx)
      end
      | HypEq _ _ = raise Match

    fun Eq r alpha (jdg as _ |> _ >> TRUE (P, _)) =
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
               ORELSE VoidRules.TypeEq alpha
               ORELSE HypEq alpha) jdg
         | _ => raise Fail "Eq not applicable")
      | Eq _ _ _ = raise Match

    fun Ext alpha (jdg as _ |> _ >> TRUE (P, _)) =
      (case out P of
           CTT (EQ _) $ _ =>
             PiRules.Ext alpha jdg
        | _ => raise Fail "Ext not applicable")
      | Ext _ _ = raise Match
  end

  fun Witness m alpha (G |> H >> TRUE (P, _)) =
    let
      val (goal, _, _) =
        makeGoal @@
          [] |> makeMemberSequent H (m, P)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        makeEvidence G H m)
    end
    | Witness _ _ _ = raise Match

  fun Hyp i _ (G |> H >> TRUE (P, _)) =
    let
      val (Q, tau) = Ctx.lookup (getHyps H) i
    in
      if Abt.eq (P, Q) then
        (T.empty, fn rho =>
          makeEvidence G H @@
            check' (`i , tau))
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
    fun Unfold sign opid target _ jdg =
      let
        open SmallStep DynamicsUtil
        fun go m =
          case out m of
               CUST (opid', _, _) $ _ =>
                 if Symbol.eq (opid, opid') then
                   case step' sign m of
                        FINAL => m
                      | STEP m' => m'
                 else
                   m
             | _ => m
        val deepGo = go o Abt.deepMapSubterms go
        val jdg' = Target.targetRewrite deepGo target jdg
        val (goal, _, _) = makeGoal jdg'
        val psi = T.empty @> goal
      in
        (psi, fn rho =>
          T.lookup rho (#1 goal))
      end

    fun Normalize sign target _ jdg =
      let
        open SmallStep DynamicsUtil
        fun go m = evalOpen sign m handle _ => m
        val deepGo = go o Abt.deepMapSubterms go

        val jdg' = Target.targetRewrite deepGo target jdg
        val (goal, _, _) = makeGoal jdg'
        val psi = T.empty @> goal
      in
        (psi, fn rho =>
          T.lookup rho (#1 goal))
      end

    fun RewriteGoal Q _ (G |> H >> TRUE (P, sigma)) =
      let
        val tau = sort P
        val (ceqGoal, _, _) =
          makeGoal @@
            [] |> H >> TRUE (check (getMetas H) (CTT (CEQUIV tau) $ [([],[]) \ P, ([],[]) \ Q], EXP), EXP)

        val (mainGoal, _, _) =
          makeGoal @@
            [] |> H >> TRUE (Q, sigma)

        val psi = T.empty @> ceqGoal @> mainGoal
      in
        (psi, fn rho =>
          makeEvidence G H @@
            T.lookup rho (#1 mainGoal) // ([],[]))
      end
      | RewriteGoal _ _ _ = raise Match

    fun EvalGoal sign target _ jdg =
      let
        val jdg' = Target.targetRewrite (DynamicsUtil.evalOpen sign) target jdg
        val (goal, _, _) = makeGoal jdg'
        val psi = T.empty @> goal
      in
        (psi, fn rho =>
          T.lookup rho (#1 goal))
      end

    local
      open LevelOperatorData
      val lbase = check' (LVL_OP LBASE $ [], LVL)
    in
      fun inferTypeLevel (H : Sequent.context) P =
        case out P of
            CTT (UNIV _) $ [_ \ i] => check (getMetas H) (LVL_OP LSUCC $ [([],[]) \ i], LVL)
          | CTT (BASE _) $ _ => lbase
          | CTT (CEQUIV _) $ _ => lbase
          | CTT (CAPPROX _) $ _ => lbase
          | CTT (EQ _) $ _ => lbase
          | CTT (SQUASH _) $ [_ \ a] => inferTypeLevel H a (* we may be able to make this just [lbase] *)
          | ATM (ATOM _) $ _ => lbase
          | `x =>
              let
                val (univ, _) = Ctx.lookup (getHyps H) x
                val (_, i) = destUniv univ
              in
                i
              end
          | _ => raise Fail "Level inference heuristic failed"
    end

    fun ProveIsType alpha =
      fn jdg as _ |> H >> TYPE (P, tau) =>
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
            ORELSE EvalGoal sign Target.TARGET_CONCL alpha
  end
end
