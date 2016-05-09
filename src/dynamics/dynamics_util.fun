functor DynamicsUtil (D : DYNAMICS) : DYNAMICS_UTIL =
struct
  open D D.SmallStep D.Signature
  infix <:

  structure Env = Abt.Variable.Ctx
  structure MetaEnv = Abt.Metavariable.Ctx
  structure SymEnv = Abt.Symbol.Ctx

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

  fun stepn sign n =
    let
      fun go i cl =
        if i < n then
          case step sign cl of
               FINAL => cl
             | STEP cl' => go (i + 1) cl'
        else
          cl
    in
      fn m => force (go 0 (m <: empty))
    end

  fun step' sign m =
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
      val rho = Env.foldl (fn (x,tau,r) => Env.insert r x (check (` x, tau))) Env.empty (varctx m)
    in
      eval sign (MetaEnv.empty, srho, rho) m
    end
end

structure DynamicsUtil = DynamicsUtil (Dynamics)
