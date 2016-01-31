signature DYNAMICS =
sig
  structure SmallStep : SMALL_STEP
  structure Signature : ABT_SIGNATURE

  type abt = Signature.Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign
  type env = Signature.Abt.varenv

  datatype 'a closure = <: of 'a * env
  exception STUCK of abt

  val step : sign -> abt closure -> abt closure step
  val step' : sign -> abt -> abt closure step
end
