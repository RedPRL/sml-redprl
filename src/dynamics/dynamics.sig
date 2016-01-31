signature DYNAMICS =
sig
  structure Abt : ABT
  structure SmallStep : SMALL_STEP
  structure Signature : ABT_SIGNATURE

  type abt = Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign
  type env = Abt.varenv

  datatype 'a closure = <: of 'a * env
  exception STUCK of abt

  val step : sign -> abt closure -> abt closure step
  val step' : sign -> abt -> abt closure step
end
