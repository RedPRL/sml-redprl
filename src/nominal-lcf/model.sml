structure NominalLcfModel :
sig
  include NOMINAL_LCF_MODEL
  exception RefinementError of Pos.t option * exn
end =
struct
  structure R = Refiner
  structure Syn = NominalLcfSyntax
  structure RSyn = RedPrlAbtSyntax
  structure Lcf = RefinerKit.Lcf
  structure T = RefinerKit.Tacticals

  structure LcfUtil = LcfUtil (Lcf)

  structure MT = Multitacticals (Lcf)
  structure Tele = Lcf.T
  structure Spr = UniversalSpread

  type 'a nominal = Syn.atom Spr.point -> 'a

  type tactic = T.Lcf.tactic nominal
  type multitactic = Lcf.multitactic nominal

  (* signature *)
  type env = tactic Syn.VarCtx.dict

  exception InvalidRule

  fun Trace m jdg =
    (print (ShowAbt.toString m ^ "\n");
     LcfUtil.unit jdg)

  val optionToTarget =
    fn NONE => Target.TARGET_CONCL
     | SOME a => Target.TARGET_HYP a

  fun rule' (sign, rho) (tac : RedPrlAbt.abt) : tactic =
    case RSyn.out tac of
         RSyn.TAC_ID => (fn _ => T.ID)
       | RSyn.TAC_FAIL => (fn _ => fn _ => raise Fail "Fail")
       | RSyn.TAC_TRACE (_, m) => (fn _ => Trace m)
       | RSyn.TAC_ELIM (u, _) => R.Elim u
       | RSyn.TAC_ETA (u, _) => R.Eta u
       | RSyn.TAC_HYP (u, _) => R.Hyp u
       | RSyn.TAC_UNHIDE (u, _) => R.Unhide u
       | RSyn.TAC_INTRO _ => R.Intro
       | RSyn.TAC_EQ r => R.Eq r
       | RSyn.TAC_EXT => R.Ext
       | RSyn.TAC_CHKINF => R.CheckInfer
       | RSyn.TAC_CUM => R.Cum
       | RSyn.TAC_CSTEP i => R.CStep sign i
       | RSyn.TAC_CSYM => R.CSym
       | RSyn.TAC_CEVAL => R.CEval sign
       | RSyn.TAC_REWRITE_GOAL (tau, m) => R.RewriteGoal m
       | RSyn.TAC_EVAL_GOAL u => R.EvalGoal sign (optionToTarget u)
       | RSyn.TAC_WITNESS (tau, m) => R.Witness m
       | RSyn.TAC_UNFOLD (opid, u) => R.Unfold sign opid (optionToTarget u)
       | RSyn.TAC_NORMALIZE u => R.Normalize sign (optionToTarget u)
       | RSyn.TAC_AUTO => R.AutoStep sign
       | _ => raise InvalidRule

  exception RefinementError of Pos.t option * exn

  fun rule (sign, rho) (tac : RedPrlAbt.abt) alpha goal =
    rule' (sign, rho) tac alpha goal
      handle exn => raise RefinementError (RSyn.getAnnotation tac, exn)
end
