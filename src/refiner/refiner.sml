structure Refiner : REFINER =
struct
  structure Abt = Abt
  open RefinerKit

  open Sequent
  infix $ \ @@ @> $#
  infix 4 >>
  infix 3 |>

  structure HoleUtil = HoleUtil (structure Tm = Abt and J = Judgment and T = T)

  fun stateToString (psi, vld) =
    let
      open T.ConsView
      fun go i =
        fn EMPTY => (T.empty, "")
         | CONS (x, jdg, tl) =>
             let
               val var = Metavariable.named ("?" ^ Int.toString i)
               val goal = "\nHOLE " ^ Metavariable.toString var ^ "\n--------------------------------------------\n" ^ Judgment.judgmentToString jdg
               val vartm = HoleUtil.makeHole (var, Judgment.evidenceValence jdg)
               val tl' = Telescope.map (Judgment.substJudgment (x, vartm)) tl
               val (rho, rest) = go (i + 1) (out tl')
             in
               (T.snoc rho x vartm, goal ^ "\n" ^ rest)
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

    fun HypEq alpha (G |> H >> TRUE (P, _)) =
      let
        val (_, m, n, a) = destEq P
        val x = destVar m
        val y = destVar n
        val _ = if Variable.eq (x, y) then () else raise Match
        val (a', _) = Ctx.lookup (#hypctx H) x
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
  end

  fun Witness m alpha (G |> H >> TRUE (P, _)) =
    let
      val goal =
        (newMeta "",
         [] |> makeMemberSequent H (m, P))
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        makeEvidence G H m)
    end
    | Witness _ _ _ = raise Match

  fun Hyp i _ (G |> H >> TRUE (P, _)) =
    let
      val (Q, tau) = Ctx.lookup (#hypctx H) i
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

    fun Unfold sign opid _ (G |> H >> TRUE (P, tau)) =
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

        val P' = go (Abt.deepMapSubterms go P)
        val goal =
          (newMeta "",
           [] |> H >> TRUE (P', tau))
        val psi = T.empty @> goal
      in
        (psi, fn rho =>
          let
            val _ \ ev = outb @@ T.lookup rho (#1 goal)
          in
            makeEvidence G H ev
          end)
      end
      | Unfold _ _ _ _ = raise Match

    fun Normalize sign _ (G |> H >> TRUE (P, tau)) =
      let
        open SmallStep DynamicsUtil
        fun go m = evalOpen sign m handle _ => m

        val P' = go (Abt.deepMapSubterms go P)
        val goal =
          (newMeta "",
           [] |> H >> TRUE (P', tau))
        val psi = T.empty @> goal
      in
        (psi, fn rho =>
          let
            val _ \ ev = outb @@ T.lookup rho (#1 goal)
          in
            makeEvidence G H ev
          end)
      end
      | Normalize _ _ _ = raise Match

    fun RewriteGoal Q _ (G |> H >> TRUE (P, sigma)) =
      let
        val tau = sort P
        val ceqGoal =
          (newMeta "",
           [] |> H >> TRUE (check (#metactx H) (CTT (CEQUIV tau) $ [([],[]) \ P, ([],[]) \ Q], EXP), EXP))
        val mainGoal = (newMeta "", [] |> H >> TRUE (Q, sigma))
        val psi = T.empty @> ceqGoal @> mainGoal
      in
        (psi, fn rho =>
          let
            val _ \ ev = outb @@ T.lookup rho (#1 mainGoal)
          in
            makeEvidence G H ev
          end)
      end
      | RewriteGoal _ _ _ = raise Match

    fun EvalGoal sign _ (G |> H >> TRUE (P, sigma)) =
      let
        val Q = DynamicsUtil.evalOpen sign P
        val x = newMeta ""
        val psi = T.empty @> (x, [] |> H >> TRUE (Q, sigma))
      in
        (psi, fn rho =>
          let
            val _ \ ev = outb @@ T.lookup rho x
          in
            makeEvidence G H ev
          end)
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
            ORELSE EvalGoal sign alpha
  end
end
