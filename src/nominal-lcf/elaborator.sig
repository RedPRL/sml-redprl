signature LCF_ELABORATOR =
sig
  structure Refiner : REFINER
  type abt = Abt.abt
  type env = Refiner.ntactic Abt.VarCtx.dict

  val elaborate : AbtSignature.sign -> env -> abt -> Refiner.ntactic
  val elaborate' : AbtSignature.sign -> abt -> Refiner.ntactic
end
