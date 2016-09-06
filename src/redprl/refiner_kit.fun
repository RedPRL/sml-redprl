structure Lcf = DependentLcf (RedPrlJudgment)
structure Tacticals = Tacticals (Lcf)
structure Multitacticals = Multitacticals (Lcf)

functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure E = RedPrlError and O = RedPrlOpData and T = Lcf.T and Abt = RedPrlAbt
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent

  structure CJ = RedPrlCategoricalJudgment

  fun @@ (f, x) = f x
end


