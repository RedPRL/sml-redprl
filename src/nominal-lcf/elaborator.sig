signature LCF_ELABORATOR =
sig
  structure Signature : ABT_SIGNATURE

  type symbol = Signature.Abt.symbol
  type abt = Signature.Abt.abt

  structure Refiner : REFINER
    where type symbol = symbol
    where type abt = abt

  type env = Refiner.ntactic Signature.Abt.VarCtx.dict

  val elaborate : Signature.sign -> env -> abt -> Refiner.ntactic
  val elaborate' : Signature.sign -> abt -> Refiner.ntactic
end
