structure NominalLcfModel : NOMINAL_LCF_MODEL =
struct
  structure R = Refiner
  structure Syn = NominalLcfSyntax
  structure T = RefinerKit.Tacticals
  structure Lcf = RefinerKit.Lcf

  structure LcfUtil = LcfUtil (Lcf)

  structure MT = Multitacticals (Lcf)
  structure Tele = Lcf.T
  structure Spr = UniversalSpread

  type 'a nominal = Syn.atom Spr.point -> 'a

  type tactic = Lcf.tactic nominal
  type multitactic = Lcf.multitactic nominal

  (* signature *)
  type env = tactic Syn.VarCtx.dict

  local
    open Abt OperatorData NominalLcfOperatorData
    infix $ \
  in
    exception InvalidRule

    fun Trace m jdg =
      (print (ShowAbt.toString m ^ "\n");
       LcfUtil.unit jdg)

    val optionToTarget =
      fn NONE => Target.TARGET_CONCL
       | SOME a => Target.TARGET_HYP a

    fun rule (sign, rho) tac =
      case out tac of
           LCF ID $ _ => (fn _ => T.ID)
         | LCF FAIL $ _ => (fn _ => fn _ => raise Fail "Fail")
         | LCF (TRACE _) $ [_ \ m] => (fn _ => Trace m)
         | LCF (ELIM (target, _)) $ [] =>
             R.Elim target
         | LCF (HYP (target, _)) $ [] =>
             R.Hyp target
         | LCF (UNHIDE (target, _)) $ [] =>
             R.Unhide target
         | LCF (INTRO {rule}) $ [] =>
             R.Intro (* rule *)
         | LCF (EQ {rule}) $ [] =>
             R.Eq rule
         | LCF EXT $ [] =>
             R.Ext
         | LCF CHKINF $ [] =>
             R.CheckInfer
         | LCF CUM $ [] =>
             R.Cum
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
         | _ => raise InvalidRule
  end

end
