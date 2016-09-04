structure LcfModel : NOMINAL_LCF_MODEL =
struct
  structure Syn = LcfSyntax
  structure Lcf = DependentLcf (RedPrlJudgment)
  structure T = Tacticals (Lcf)
  structure MT = Multitacticals (Lcf)
  structure Spr = UniversalSpread

  type 'a nominal = Syn.atom Spr.point -> 'a
  type tactic = MT.Lcf.tactic nominal
  type multitactic = MT.Lcf.multitactic nominal
  type env = tactic Syn.VarCtx.dict

  fun rule (sign, env) rule =
    raise Fail "TODO!"
end

structure LcfSemantics = NominalLcfSemantics (LcfModel)
