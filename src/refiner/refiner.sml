structure Refiner : REFINER =
struct
  structure Abt = RedPrlAbt
  open RefinerKit

  open Sequent
  infix $ $$ \ @@ @> $#
  infix 2 //
  infix 4 >> |>

  local
    open Tacticals
    infix ORELSE
  in
    fun Elim i alpha =
      BaseRules.Elim i alpha
        ORELSE EnsembleRules.Elim i alpha
        ORELSE VoidRules.Elim i alpha

    fun Eta i alpha =
      CEquivRules.Eta i alpha

    fun HypEq alpha (H >> EQ_MEM (m, n, a)) =
      let
        val x = Syn.destVar m
        val y = Syn.destVar n
        val _ = if Variable.eq (x, y) then () else raise Match
        val (a', _) = Ctx.lookup (getHyps H) x
        val _ = if Abt.eq (a,a') then () else raise Match
      in
        (T.empty, fn rho =>
          abtToAbs @@ Syn.into Syn.AX)
      end
      | HypEq _ _ = raise Match

    fun HypSynth alpha (H >> SYN r) =
      let
        val x = Syn.destVar r
        val (a, _) = Ctx.lookup (getHyps H) x
      in
        (T.empty, fn rho =>
           abtToAbs a)
      end
      | HypSynth _ _ = raise Match


    fun IsType' alpha (goal as H >> TYPE (a, _)) =
        (case Syn.out a of
            Syn.ATOM _ => AtomRules.IsType alpha goal
          | Syn.TOP _ => TopRules.IsType alpha goal
          | Syn.DFUN _ => PiRules.IsType alpha goal
          | Syn.ENSEMBLE _ => EnsembleRules.IsType alpha goal
          | Syn.DEP_ISECT _ => DepIsectRules.IsType alpha goal
          | Syn.CEQUIV _ => CEquivRules.IsType alpha goal
          | Syn.RECORD_TY _ => RecordRules.IsType alpha goal
          | Syn.UNIV _ => UnivRules.IsType alpha goal
          | Syn.EQ _ => EqRules.IsType alpha goal
          | _ => raise Match)
      | IsType' _ _ = raise Match

    fun IsType alpha =
      IsType' alpha
        ORELSE TypeRules.Synth alpha

    (* TODO! need to use Nominal LCF version of THEN, or else names will get
     * muddled ! *)
    and Synth alpha =
      HypSynth alpha
        ORELSE PiRules.ApSynth alpha
        ORELSE RecordRules.ProjSynth alpha
        ORELSE (THEN (SynthRules.SynthType alpha, IsType alpha))

    fun Intro alpha (goal as G |> _) = GenericRules.Intro alpha goal
      | Intro alpha (goal as H >> TRUE (a, _)) =
        (case Syn.out a of
            Syn.SQUASH _ => SquashRules.Intro alpha goal
          | Syn.ENSEMBLE _ => EnsembleRules.Intro alpha goal
          | Syn.DFUN _ => PiRules.Intro alpha goal
          | Syn.EQ _ => EqRules.Intro alpha goal
          | Syn.RECORD_TY _ => RecordRules.Intro alpha goal
          | Syn.TOP SortData.EXP => TopRules.IntroTrivial alpha goal
          | _ => raise Match)
      | Intro alpha (goal as H >> MEM _) = MemRules.Intro alpha goal
      | Intro _ _ = raise Match

    val CheckInfer = SynthRules.CheckToSynth

    fun Eq r alpha (goal as _ >> EQ_MEM (m, n, a)) =
      (case (Syn.outOpen m, Syn.outOpen n, Syn.out a) of
          (Syn.VAR _, _, _) => HypEq alpha goal
        | (Syn.APP (Syn.UNIV _), _, _) => UnivRules.Eq alpha goal
        | (Syn.APP (Syn.BASE _), _, _) => BaseRules.TypeEq alpha goal
        | (_, _, Syn.BASE _) => BaseRules.MemberEq alpha goal
        | (Syn.APP (Syn.TOP _), _, _) => TopRules.TypeEq alpha goal
        | (_, _, Syn.TOP _) => TopRules.MemberEq alpha goal
        | (Syn.APP (Syn.CEQUIV _), _, _) => CEquivRules.TypeEq alpha goal
        | (_, _, Syn.CEQUIV _) => CEquivRules.MemberEq alpha goal
        | (Syn.APP (Syn.SQUASH _), _, _) => SquashRules.TypeEq alpha goal
        | (Syn.APP (Syn.ENSEMBLE _), _, _) => EnsembleRules.TypeEq alpha goal
        | (_, _, Syn.ENSEMBLE _) => EnsembleRules.MemberEq alpha goal
        | (Syn.APP (Syn.RECORD_TY _), _, _) => RecordRules.TypeEq alpha goal
        | (_, _, Syn.RECORD_TY _) => RecordRules.MemberEq alpha goal
        | (Syn.APP (Syn.ATOM _), _, _) => AtomRules.TypeEq alpha goal
        | (_, _, Syn.ATOM _) => AtomRules.MemberEq alpha goal
        | (Syn.APP (Syn.IF_EQ _), _, _) => AtomRules.TestEq alpha goal
        | (Syn.APP (Syn.DFUN _), _, _) => PiRules.TypeEq alpha goal
        | (_, _, Syn.DFUN _) => PiRules.MemberEq alpha goal
        | (Syn.APP (Syn.DEP_ISECT _), _, _) => DepIsectRules.TypeEq alpha goal
        | (_, _, Syn.DEP_ISECT _) => DepIsectRules.MemberEq alpha goal
        | (Syn.APP Syn.VOID, _, _) => VoidRules.TypeEq alpha goal
        | _ => raise Match)
      | Eq r alpha (jdg as _ >> EQ_SYN _) =
          SynthRules.SynthEqIntro alpha jdg
      | Eq _ _ _ = raise Match

    fun Ext alpha (jdg as _ >> TRUE (P, _)) =
      (case Syn.out P of
           Syn.EQ _ => PiRules.Ext alpha jdg
        | _ => raise Fail "Ext not applicable")
      | Ext _ _ = raise Match
  end

  fun Witness m alpha (H >> TRUE (P, _)) =
    let
      val (goal, _, _) =
        makeGoal @@
          makeMemberSequent H (m, P)
      val psi = T.empty @> goal
    in
      (psi, fn rho =>
        abtToAbs m)
    end
    | Witness _ _ _ = raise Match

  fun Hyp i _ (H >> TRUE (P, _)) =
    let
      val (Q, tau) = Ctx.lookup (getHyps H) i
    in
      if Abt.eq (P, Q) then
        (T.empty, fn rho =>
           abtToAbs @@ check (`i , RS.EXP tau))
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
    exception TODO
    open SortData
  in
    fun Unfold sign opid target _ jdg =
      let
        fun go m =
          case out m of
               RedPrlOperator.CUSTOM (opid', _, _) $ _ =>
                 if Symbol.eq (opid, opid') then
                   RedPrlDynamics.stepN sign 1 m
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
        fun go m = RedPrlDynamics.eval sign m handle _ => m
        val deepGo = go o Abt.deepMapSubterms go

        val jdg' = Target.targetRewrite deepGo target jdg
        val (goal, _, _) = makeGoal jdg'
        val psi = T.empty @> goal
      in
        (psi, fn rho =>
          T.lookup rho (#1 goal))
      end

    fun RewriteGoal Q _ (H >> TRUE (P, sigma)) =
      let
        val RS.EXP tau = sort P
        val (ceqGoal, _, _) =
          makeGoal @@
            H >> TRUE (Syn.into @@ Syn.CEQUIV (tau, P, Q), EXP)

        val (mainGoal, _, _) =
          makeGoal @@
            H >> TRUE (Q, sigma)

        val psi = T.empty @> ceqGoal @> mainGoal
      in
        (psi, fn rho =>
          T.lookup rho (#1 mainGoal))
      end
      | RewriteGoal _ _ _ = raise Match

    fun EvalGoal sign target _ jdg =
      let
        val jdg' = Target.targetRewrite (RedPrlDynamics.eval sign) target jdg
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
            ORELSE GenericRules.Intro alpha
  end
end
