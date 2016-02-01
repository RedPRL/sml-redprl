functor DynamicsUtil (D : DYNAMICS) : DYNAMICS_UTIL =
struct
  open D D.SmallStep D.Signature
  infix <:

  structure Env = Abt.VarCtx
  structure MetaEnv = Abt.MetaCtx
  structure SymEnv = Abt.SymCtx

  val empty =
    (MetaEnv.empty, SymEnv.empty, Env.empty)

  fun force (m <: (mrho, srho, rho)) =
    let
      val mrho' = MetaEnv.map forceB mrho
      val rho' = Env.map force rho
    in
      Abt.renameEnv srho (Abt.substEnv rho' (Abt.metasubstEnv mrho' m))
    end
  and forceB (e <: env) =
    Abt.mapAbs (fn m => force (m <: env)) e

  fun step' sign m : abt step =
    SmallStep.map
      force
      (step sign (m <: empty))

  fun eval sign (mrho, srho, rho) : abt -> abt =
    let
      fun go cl =
        case step sign cl of
             FINAL => cl
           | STEP cl' => go cl'
      fun initiate m =
        m <: (MetaEnv.map (fn x => x <: empty) mrho, srho, Env.map (fn x => x <: empty) rho)
    in
      force o go o initiate
    end

  fun evalClosed sign : abt -> abt =
    eval sign empty

  fun evalOpen sign m =
    let
      open Abt
      val srho = SymEnv.foldl (fn (u,_,r) => SymEnv.insert r u u) SymEnv.empty (symctx m)
      val rho = Env.foldl (fn (x,tau,r) => Env.insert r x (check' (` x, tau))) Env.empty (varctx m)
    in
      eval sign (MetaEnv.empty, srho, rho) m
    end
end

structure DynamicsUtil = DynamicsUtil (Dynamics)
