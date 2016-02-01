signature DYNAMICS =
sig
  structure SmallStep : SMALL_STEP
  structure Signature : ABT_SIGNATURE

  type abt = Signature.Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign

  type 'a env = 'a Signature.Abt.VarCtx.dict
  datatype closure = <: of abt * (closure env * Signature.Abt.metaenv)

  val step : sign -> closure -> closure step
  exception Stuck of closure
end
