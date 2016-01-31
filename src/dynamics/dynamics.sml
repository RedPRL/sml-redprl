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

  open SmallStep

  datatype 'a closure = <: of 'a * 'a closure env
  infix <:

  exception STUCK of abt

  open Abt infix $ \

  exception hole
  fun ?x = raise x

  fun step sign (m <: rho) : abt closure step =
    case out m of
         `x => ret (Env.lookup rho x)
       | _ => ?hole

end
