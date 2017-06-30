functor NewMachine (Sig : MINI_SIGNATURE) :
sig
  type sign = Sig.sign
  type abt = RedPrlAbt.abt
  type 'a machine

  val step : sign -> abt machine -> abt machine
end = 
struct
  structure Tm = RedPrlAbt

  type sign = Sig.sign

  datatype 'a closure = <: of 'a * environment
  withtype param_env = Tm.param Sym.Ctx.dict
  and object_env = Tm.abt closure Var.Ctx.dict
  and meta_env = Tm.abt closure Tm.bview Metavar.Ctx.dict
  and environment = meta_env * object_env * param_env

  datatype continuation = DUMMY

  type frame = continuation * environment
  type stack = frame list
  datatype 'a machine = || of 'a closure * stack

  infix 5 <:
  infix 3 ||

  open Tm infix $ $$ $# \
  structure O = RedPrlOpData
  structure P = RedPrlParameterTerm

  datatype blocker =
     VAR of variable
   | METAVAR of metavariable

  exception Neutral of blocker

  fun lookupSym psi x = 
    Sym.Ctx.lookup psi x
    handle Sym.Ctx.Absent => P.ret x

  fun readParam (psi : param_env) : param -> param = 
    P.bind (lookupSym psi)

  fun step sign state =
    let
      val tm <: env || stk = state
      val (mrho, rho, psi) = env
    in
      case out tm of 
         `x => (Var.Ctx.lookup rho x || stk handle Var.Ctx.Absent => raise Neutral (VAR x))
       | meta $# (ps, ms) =>
         let
           val (us, xs) \ m <: (mrho', rho', psi') = Metavar.Ctx.lookup mrho meta handle Metavar.Ctx.Absent => raise Neutral (METAVAR meta)
           val rho'' = ListPair.foldl (fn (x, n, rho) => Var.Ctx.insert rho x (n <: env)) rho' (xs, ms)
           val psi'' = ListPair.foldl (fn (u, (r, _), psi) => Sym.Ctx.insert psi u (readParam psi r)) psi' (us, ps)
         in
           m <: (mrho', rho'', psi'') || stk
         end
       | _ $ _ => raise Fail "TODO"
    end
end