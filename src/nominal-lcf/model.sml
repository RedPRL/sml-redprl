structure NominalLcfModel : NOMINAL_LCF_MODEL =
struct
  structure R = Refiner
  structure Syn = NominalLcfSyntax
  structure T = R.Tacticals
  structure Lcf = T.Lcf
  structure Tele = Lcf.T

  type 'a seq = int -> 'a

  type tactic = Syn.symbol seq -> Lcf.tactic
  type multitactic = Syn.symbol seq -> Lcf.multitactic

  (* signature *)
  type env = tactic Syn.VarCtx.dict

  type ('syn, 'sem) interp = Syn.sign * env -> 'syn -> 'sem

  local
    open Abt OperatorData NominalLcfOperatorData
    infix $ \
  in
    exception InvalidTactic

    fun Trace m jdg =
      let
        val x = Abt.Metavariable.named "?"
        val psi = Tele.snoc Tele.empty x jdg
      in
        print (ShowAbt.toString m ^ "\n");
        (psi, fn rho => Tele.lookup rho x)
      end

    fun Rec f alpha jdg =
      f (Rec f) alpha jdg

    val optionToTarget =
      fn NONE => Target.TARGET_CONCL
       | SOME a => Target.TARGET_HYP a

    fun tacticR f (sign, rho) tac =
      case out tac of
           LCF ORELSE $ [_ \ t1, _ \ t2] =>
             let
               val T1 = f (sign, rho) t1
               val T2 = f (sign, rho) t2
             in
               fn alpha => fn jdg =>
                 T1 alpha jdg
                   handle _ => T2 alpha jdg
             end
         | LCF ID $ _ => (fn _ => T.ID)
         | LCF FAIL $ _ => (fn _ => fn _ => raise Fail "Fail")
         | LCF (TRACE _) $ [_ \ m] => (fn _ => Trace m)
         | LCF PROGRESS $ [_ \ t] =>
             T.PROGRESS o f (sign, rho) t
         | LCF (ELIM (target, _)) $ [] =>
             R.Elim target
         | LCF (HYP (target, _)) $ [] =>
             R.Hyp target
         | LCF (UNHIDE (target, _)) $ [] =>
             R.Unhide target
         | LCF (INTRO {rule}) $ [] =>
             R.Intro rule
         | LCF (EQ {rule}) $ [] =>
             R.Eq rule
         | LCF EXT $ [] =>
             R.Ext
         | LCF (CSTEP i) $ [] =>
             R.CStep sign i
         | LCF CSYM $ [] =>
             R.CSym
         | LCF CEVAL $ [] =>
             R.CEval sign
         | LCF (REWRITE_GOAL tau) $ [_ \ m] =>
             R.RewriteGoal m
         | LCF (EVAL_GOAL targ) $ [] =>
             R.EvalGoal sign (optionToTarget targ)
         | LCF (WITNESS tau) $ [_ \ m] =>
             R.Witness m
         | LCF (UNFOLD (opid, targ)) $ [] =>
             R.Unfold sign opid (optionToTarget targ)
         | LCF (NORMALIZE targ) $ [] =>
             R.Normalize sign (optionToTarget targ)
         | LCF AUTO $ [] =>
             R.AutoStep sign
         | LCF REC $ [(_, [x]) \ t] =>
             Rec (fn T => f (sign, VarCtx.insert rho x T) t)
         | _ => raise InvalidTactic
  end

end
