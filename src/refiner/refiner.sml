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

    fun HypEq alpha (G |> H >> EQ_MEM (m, n, a)) =
      let
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

    fun HypSynth alpha (G |> H >> SYN r) =
      let
        val x = destVar r
        val (a, _) = Ctx.lookup (getHyps H) x
      in
        (T.empty, fn rho =>
          makeEvidence G H a)
      end
      | HypSynth _ _ = raise Match

    fun IsType alpha =
      AtomRules.IsType alpha
        ORELSE BaseRules.IsType alpha
        ORELSE TopRules.IsType alpha
        ORELSE PiRules.IsType alpha
        ORELSE EnsembleRules.IsType alpha
        ORELSE DepIsectRules.IsType alpha
        ORELSE CEquivRules.IsType alpha
        ORELSE RecordRules.IsType alpha
        ORELSE UnivRules.IsType alpha
        ORELSE TypeRules.Synth alpha

    (* TODO! need to use Nominal LCF version of THEN, or else names will get
     * muddled ! *)
    and Synth alpha =
      HypSynth alpha
        ORELSE PiRules.ApSynth alpha
        ORELSE RecordRules.ProjSynth alpha
        ORELSE (THEN (SynthRules.SynthType alpha, IsType alpha))

    fun Intro alpha =
      SquashRules.Intro alpha
        ORELSE EnsembleRules.Intro alpha
        ORELSE PiRules.Intro alpha
        ORELSE EqRules.Intro alpha
        ORELSE MemRules.Intro alpha

    val CheckInfer = SynthRules.CheckToSynth

    fun Eq r alpha (jdg as _ |> _ >> EQ_MEM _) =
          (HypEq alpha
            ORELSE UnivRules.Eq alpha
            ORELSE BaseRules.TypeEq alpha
            ORELSE BaseRules.MemberEq alpha
            ORELSE TopRules.TypeEq alpha
            ORELSE TopRules.MemberEq alpha
            ORELSE CEquivRules.TypeEq alpha
            ORELSE CEquivRules.MemberEq alpha
            ORELSE SquashRules.TypeEq alpha
            ORELSE EnsembleRules.TypeEq alpha
            ORELSE EnsembleRules.MemberEq alpha
            ORELSE RecordRules.TypeEq alpha
            ORELSE RecordRules.MemberEq alpha
            ORELSE AtomRules.TypeEq alpha
            ORELSE AtomRules.MemberEq alpha
            ORELSE AtomRules.TestEq alpha
            ORELSE PiRules.TypeEq alpha
            ORELSE PiRules.MemberEq alpha
            ORELSE DepIsectRules.TypeEq alpha
            ORELSE DepIsectRules.MemberEq alpha
            ORELSE VoidRules.TypeEq alpha) jdg
      | Eq r alpha (jdg as _ |> _ >> EQ_SYN _) =
          SynthRules.SynthEqIntro alpha jdg
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

  val Cum =
    UnivRules.Cum

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
  end

  local
    open Tacticals
    infix 2 ORELSE
  in
    fun AutoStep sign alpha : Lcf.tactic =
        TRY @@
          IsType alpha
            ORELSE Intro alpha
            ORELSE Eq NONE alpha
            ORELSE PROGRESS (EvalGoal sign Target.TARGET_CONCL alpha)
            ORELSE PROGRESS (CStep sign 0 alpha)
            ORELSE Synth alpha
  end
end
