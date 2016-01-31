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
