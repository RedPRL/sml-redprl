structure Dynamics : DYNAMICS =
struct
  structure Abt = Abt
  structure SmallStep = SmallStep
  structure Signature = AbtSignature
  structure Env = Abt.VarCtx

  type abt = Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign
  type env = Abt.varenv

  open SmallStep

  datatype 'a closure = <: of 'a * env
  infix <:

  exception STUCK of abt

  exception hole
  fun ?x = raise x

  fun step sign (m <: rho) : abt closure step =
    ?hole

  fun step' sign m =
    step sign (m <: Env.empty)
end
