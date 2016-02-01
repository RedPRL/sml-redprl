functor DynamicsUtil (D : DYNAMICS) : DYNAMICS_UTIL =
struct
  open D D.SmallStep D.Signature
  infix <:

  structure Env = Abt.VarCtx
  structure MetaEnv = Abt.MetaCtx

  val empty =
    (MetaEnv.empty, Env.empty)

  fun force (m <: (mrho, rho)) =
    let
      val mrho' = MetaEnv.map forceB mrho
      val rho' = Env.map force rho
    in
      Abt.metasubstEnv mrho' (Abt.substEnv rho' m)
    end
  and forceB (e <: env) =
    Abt.mapAbs (fn m => force (m <: env)) e

  fun step' sign m : abt step =
    SmallStep.map
      force
      (step sign (m <: empty))

  fun eval sign (mrho, rho) : abt -> abt =
    let
      fun go cl =
        case step sign cl of
             FINAL => cl
           | STEP cl' => go cl'
      fun initiate m =
        m <: (MetaEnv.map (fn x => x <: empty) mrho, Env.map (fn x => x <: empty) rho)
    in
      force o go o initiate
    end

  fun eval' sign : abt -> abt =
    eval sign empty
end

structure DynamicsUtil = DynamicsUtil (Dynamics)
