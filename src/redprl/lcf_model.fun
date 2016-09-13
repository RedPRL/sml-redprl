functor LcfModel (Sig : MINI_SIGNATURE) :
sig
  include NOMINAL_LCF_MODEL
  structure Lcf : DEPENDENT_LCF
end =
struct
  structure Lcf = Lcf and T = Tacticals and MT = Multitacticals and Spr = UniversalSpread
  structure Syn = LcfSyntax (Sig)

  type 'a nominal = Syn.atom Spr.point -> 'a
  type tactic = MT.Lcf.tactic nominal
  type multitactic = MT.Lcf.multitactic nominal
  type env = tactic Syn.VarCtx.dict
  exception InvalidRule

  open RedPrlAbt
  infix $ \

  structure Rules = Refiner (Sig)

  structure O = RedPrlOpData
  fun interpret (sign, env) rule =
    case out rule of
       `x => Var.Ctx.lookup env x
     | O.MONO O.RULE_ID $ _ => (fn _ => T.ID)
     | O.MONO O.RULE_EVAL_GOAL $ _ => Rules.CEquiv.EvalGoal sign
     | O.MONO O.RULE_CEQUIV_REFL $ _ => Rules.CEquiv.Refl
     | O.MONO O.RULE_AUTO $ _ => Rules.Auto sign
     | O.POLY (O.RULE_HYP z) $ _ => Rules.Hyp.Project z
     | O.POLY (O.RULE_ELIM z) $ _ => Rules.Elim sign z
     | O.MONO O.RULE_WITNESS $ [_ \ tm] => Rules.Truth.Witness tm
     | _ => raise InvalidRule

  fun rule (sign, env) rule alpha goal =
    Debug.wrap (fn _ => interpret (sign, env) rule alpha goal)
    handle exn => raise RedPrlError.annotate (getAnnotation rule) exn
end
