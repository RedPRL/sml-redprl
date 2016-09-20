functor LcfModel (Sig : MINI_SIGNATURE) :
sig
  include NOMINAL_LCF_MODEL
  structure Lcf : DEPENDENT_LCF
end =
struct
  structure Lcf = Lcf and T = Tacticals and MT = Multitacticals and Spr = UniversalSpread and E = RedPrlError
  structure Syn = LcfSyntax (Sig)
  structure Machine = RedPrlMachine (Sig)

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
     | O.MONO O.RULE_EVAL_GOAL $ _ => Rules.Lift (Rules.CEquiv.EvalGoal sign)
     | O.MONO O.RULE_CEQUIV_REFL $ _ => Rules.Lift (Rules.CEquiv.Refl)
     | O.MONO O.RULE_AUTO_STEP $ _ => Rules.Lift (Rules.AutoStep sign)
     | O.POLY (O.RULE_HYP z) $ _ => Rules.Lift (Rules.Hyp.Project z)
     | O.POLY (O.RULE_ELIM z) $ _ => Rules.Lift (Rules.Elim sign z)
     | O.MONO O.RULE_WITNESS $ [_ \ tm] => Rules.Lift (Rules.Truth.Witness tm)
     | O.MONO O.RULE_HEAD_EXP $ _ => Rules.Lift (Rules.Equality.HeadExpansion sign)
     | O.MONO O.RULE_SYMMETRY $ _ => Rules.Lift Rules.Equality.Symmetry
     | _ => raise E.error [E.% "Invalid rule", E.! rule]

  fun rule (sign, env) rule alpha goal =
    Debug.wrap (fn _ => interpret (sign, env) (Machine.eval sign rule) alpha goal)
    handle exn => raise RedPrlError.annotate (getAnnotation rule) exn
end
