structure Refiner : REFINER =
struct
  structure Abt = Abt and Ctx = SymbolTelescope and Signature = AbtSignature

  structure Kit =
  struct
    structure Tm = Abt
    open Abt

    type judgment = Sequent.sequent
    type evidence = abs

    fun judgmentToString s =
      "{" ^ Sequent.toString s ^ "}"

    fun evidenceValence _ = (([],[]), SortData.EXP)

    fun evidenceToString e =
      let
        infix \
        val _ \ m = outb e
      in
        DebugShowAbt.toString m
      end

    open Sequent infix >>
    fun substJudgment (x, e) (H >> P) =
      Ctx.map H (metasubst (e,x))
        >> metasubst (e, x) P
  end

  open Abt

  structure Lcf = DependentLcf (Kit)
  structure Telescope = Lcf.T and T = Lcf.T
  structure Tacticals = Tacticals(Lcf)

  type 'a choice_sequence = int -> 'a
  type name_store = symbol choice_sequence
  type ntactic = name_store -> Tacticals.Lcf.tactic

  open Sequent infix >> $ \

  fun Elim i _ =
    raise Fail "To be implemented"

  fun Intro r _ =
    raise Fail "To be implemented"

  fun Hyp i _ (H >> P) =
    let
      val Q = Ctx.lookup H i
    in
      if Abt.eq (P, Q) then
        (T.empty, fn rho =>
          abtToAbs (check' (`i , SortData.EXP)))
      else
        raise Fail "Failed to unify with hypothesis"
    end

  exception hole
  fun ?x = raise x

  local
    val counter = ref 0
  in
    fun newMeta str =
      let
        val i = !counter
      in
        counter := i + 1;
        Metavariable.named ("?" ^ str ^ Int.toString i)
      end
  end


  local
    open OperatorData CttOperatorData
    fun destCEquiv P =
      case (metactx P, out P) of
           (theta, CTT (CEQUIV tau) $ [_ \ m, _ \ n]) => (theta, tau, m, n)
         | _ => raise Fail "Expected CEquiv"
    val ax = check' (CTT AX $ [], SortData.EXP)
  in
    fun CSym _ (H >> P) =
      let
        val (theta, tau, m, n) = destCEquiv P
        val x = newMeta "ceq"
        val subgoal = check theta (CTT (CEQUIV tau) $ [([],[]) \ n, ([],[]) \ m], SortData.EXP)
        val psi = T.snoc T.empty (x, Ctx.empty >> subgoal)
      in
        (psi, fn rho =>
          abtToAbs ax)
      end

    fun CStep sign i _ (H >> P) =
      let
        val (theta, tau, m, n) = destCEquiv P
        val m' = DynamicsUtil.stepn sign i m
      in
        (if Abt.eq (m', n) then
          (T.empty, fn rho =>
            abtToAbs ax)
         else
           let
             val x = newMeta "ceq"
             val subgoal = check theta (CTT (CEQUIV tau) $ [([],[]) \ m', ([],[]) \ n], SortData.EXP)
             val psi = T.snoc T.empty (x, Ctx.empty >> subgoal)
           in
             (psi, fn rho =>
               abtToAbs ax)
           end)
      end

    fun CEval sign _ (H >> P) =
      let
        val (theta, tau, m, n) = destCEquiv P
        val m' = DynamicsUtil.evalClosed sign m
      in
        (if Abt.eq (m', n) then
          (T.empty, fn rho =>
            abtToAbs ax)
         else
           let
             val x = newMeta "ceq"
             val subgoal = check theta (CTT (CEQUIV tau) $ [([],[]) \ m', ([],[]) \ n], SortData.EXP)
             val psi = T.snoc T.empty (x, Ctx.empty >> subgoal)
           in
             (psi, fn rho =>
               abtToAbs ax)
           end)
      end

  end

end
