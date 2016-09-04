functor LcfModel (Sig : MINI_SIGNATURE) :
sig
  include NOMINAL_LCF_MODEL
  structure Lcf : DEPENDENT_LCF
end =
struct
  structure Syn = LcfSyntax (Sig)
  structure Lcf = DependentLcf (RedPrlJudgment)
  structure T = Tacticals (Lcf)
  structure MT = Multitacticals (Lcf)
  structure Spr = UniversalSpread
  structure Machine = RedPrlMachine (Sig)

  type 'a nominal = Syn.atom Spr.point -> 'a
  type tactic = MT.Lcf.tactic nominal
  type multitactic = MT.Lcf.multitactic nominal
  type env = tactic Syn.VarCtx.dict

  open RedPrlAbt
  infix $ \

  structure O = RedPrlOpData
  exception InvalidRule

  fun rule (sign, env) rule =
    case out rule of
       `x => Var.Ctx.lookup env x
     | O.MONO O.TAC_ID $ _ => (fn _ => T.ID)
     | _ => raise InvalidRule
end
