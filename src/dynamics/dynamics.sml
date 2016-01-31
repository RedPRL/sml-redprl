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

  exception hole
  fun ?x = raise x

  fun step sign (m <: rho) : abt closure step =
    ?hole

end

functor DynamicsUtil (D : DYNAMICS) : DYNAMICS_UTIL =
struct
  open D D.SmallStep D.Signature
  infix <:

  structure Env = Abt.VarCtx

  fun force (m <: rho) =
    Abt.substEnv
      (Env.map force rho)
      m

  fun step' sign m =
    SmallStep.map
      force
      (step sign (m <: Env.empty))

  fun eval sign rho =
    let
      fun go cl =
        case step sign cl of
             FINAL => cl
           | STEP cl' => go cl'
      fun initiate m =
        m <: Env.map (fn x => x <: Env.empty) rho
    in
      force o go o initiate
    end

  fun eval' sign =
    eval sign Env.empty
end

structure DynamicsUtil = DynamicsUtil (Dynamics)
