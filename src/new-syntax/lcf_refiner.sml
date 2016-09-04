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
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))

  type 'a nominal = Syn.atom Spr.point -> 'a
  type tactic = MT.Lcf.tactic nominal
  type multitactic = MT.Lcf.multitactic nominal
  type env = tactic Syn.VarCtx.dict

  open RedPrlAbt
  infix $ $$ \

  structure O = RedPrlOpData
  exception InvalidRule

  structure Rules =
  struct
    structure T = Lcf.T and Abt = RedPrlAbt
    structure TeleNotation = TelescopeNotation (T)
    open RedPrlSequent TeleNotation
    structure CJ = RedPrlCategoricalJudgment
    infix |> >> >:

    fun EvalGoal sign _ jdg =
      let
        val x = Metavar.named "?"
        val jdg' = RedPrlSequent.map (CJ.map (Machine.eval sign)) jdg
        val psi = T.empty >: (x, jdg')
      in
        (psi, fn rho => T.lookup rho x)
      end

    fun CEquivRefl _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
      in
        if Abt.eq (m, n) then
          (T.empty, fn _ => abtToAbs (O.MONO O.AX $$ []))
        else
          raise Match
      end

  end

  fun rule (sign, env) rule =
    case out rule of
       `x => Var.Ctx.lookup env x
     | O.MONO O.RULE_ID $ _ => (fn _ => T.ID)
     | O.MONO O.RULE_EVAL_GOAL $ _ => Rules.EvalGoal sign
     | O.MONO O.RULE_CEQUIV_REFL $ _ => Rules.CEquivRefl
     | _ => raise InvalidRule
end
