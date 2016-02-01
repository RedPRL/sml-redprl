functor DynamicsUtil (D : DYNAMICS) : DYNAMICS_UTIL =
struct
  open D D.SmallStep D.Signature
  infix <:

  structure Env = Abt.VarCtx
  structure MetaEnv = Abt.MetaCtx

  val empty =
    (Env.empty, MetaEnv.empty)

  fun force (m <: (rho, mrho)) =
    Abt.substEnv
      (Env.map force rho)
      m

  fun step' sign m : abt step =
    SmallStep.map
      force
      (step sign (m <: empty))

  fun eval sign (rho, mrho : abs metaenv) : abt -> abt =
    let
      fun go cl =
        case step sign cl of
             FINAL => cl
           | STEP cl' => go cl'
      fun initiate m =
        m <: (Env.map (fn x => x <: empty) rho, MetaEnv.map (fn x => x <: empty) mrho)
    in
      force o go o initiate
    end

  fun eval' sign : abt -> abt =
    eval sign (Env.empty, MetaEnv.empty)
end

structure DynamicsUtil = DynamicsUtil (Dynamics)
