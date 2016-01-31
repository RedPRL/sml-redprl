signature DYNAMICS =
sig
  structure SmallStep : SMALL_STEP
  structure Signature : ABT_SIGNATURE

  type abt = Signature.Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign

  type 'a env = 'a Signature.Abt.VarCtx.dict
  datatype 'a closure = <: of 'a * 'a closure env

  val step : sign -> abt closure -> abt closure step
  exception Stuck of abt closure
end
