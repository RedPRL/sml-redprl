functor LcfModel (Sig : MINI_SIGNATURE) : NOMINAL_LCF_MODEL =
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

  fun rule (sign, env) rule =
    raise Fail "TODO!"
end

functor LcfSemantics (Sig : MINI_SIGNATURE) = NominalLcfSemantics (LcfModel (Sig))
