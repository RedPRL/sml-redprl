structure Dynamics : DYNAMICS =
struct
  structure Abt = Abt
  structure SmallStep = SmallStep
  structure Signature = AbtSignature
  structure Env = Abt.VarCtx

  type abt = Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign
  type 'a env = 'a Abt.VarCtx.dict

  datatype 'a closure = <: of 'a * 'a closure env
  exception STUCK of abt

  open SmallStep

  datatype 'a closure = <: of 'a * 'a closure env
  infix <:

  exception STUCK of abt

  exception hole
  fun ?x = raise x

  fun force (m <: rho) =
    Abt.substEnv (Env.map force rho) m

  fun step sign (m <: rho) : abt closure step =
    ?hole

  fun step' sign m =
    SmallStep.map force (step sign (m <: Env.empty))
end
