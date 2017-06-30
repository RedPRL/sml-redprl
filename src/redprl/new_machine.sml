functor NewMachine (Sig : MINI_SIGNATURE) :
sig
  type sign = Sig.sign
  type abt = RedPrlAbt.abt
  type 'a machine

  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable

  exception Neutral of blocker
  exception Unstable

  val step : sign -> stability -> abt machine -> abt machine
end = 
struct
  structure Tm = RedPrlAbt

  type sign = Sig.sign

  datatype 'a closure = <: of 'a * environment
  withtype param_env = Tm.param Sym.Ctx.dict
  and object_env = Tm.abt closure Var.Ctx.dict
  and meta_env = Tm.abt closure Tm.bview Metavar.Ctx.dict
  and environment = meta_env * object_env * param_env

  datatype hole = HOLE
  datatype continuation =
     APP of hole * Tm.abt

  type frame = continuation closure
  type stack = frame list
  datatype 'a machine = || of 'a closure * stack

  infix 5 <:
  infix 3 ||

  open Tm infix 6 $ $$ $# \
  structure O = RedPrlOpData
  structure P = RedPrlParameterTerm

  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of variable
   | METAVAR of metavariable

  exception Neutral of blocker
  exception Unstable

  val todo = Fail "TODO"
  fun ?e = raise e

  fun lookupSym psi x = 
    Sym.Ctx.lookup psi x
    handle Sym.Ctx.Absent => P.ret x

  fun readParam (psi : param_env) : param -> param = 
    P.bind (lookupSym psi)

  fun stepView sign stability = 
    fn `x <: (mrho, rho, psi) || stk =>
       (Var.Ctx.lookup rho x || stk
        handle Var.Ctx.Absent => raise Neutral (VAR x))
     | meta $# (ps, ms) <: env || stk =>
       let
         val (mrho, rho, psi) = env
         val (us, xs) \ (m <: (mrho', rho', psi')) = Metavar.Ctx.lookup mrho meta handle Metavar.Ctx.Absent => raise Neutral (METAVAR meta)
         val rho'' = ListPair.foldl (fn (x, n, rho) => Var.Ctx.insert rho x (n <: env)) rho' (xs, ms)
         val psi'' = ListPair.foldl (fn (u, (r, _), psi) => Sym.Ctx.insert psi u (readParam psi r)) psi' (us, ps)
       in
         m <: (mrho', rho'', psi'') || stk
       end
     | O.POLY (O.CUST (opid, ps, _)) $ args <: env || stk => 
       let
         val (mrho, rho, psi) = env
         val entry as {state,...} = Sig.lookup sign opid
         val term = Sig.extract state
         val (mrho', psi') = Sig.unifyCustomOperator entry (List.map #1 ps) args
         val mrho'' = Metavar.Ctx.union mrho (Metavar.Ctx.map ((fn (us,xs) \ m => (us,xs) \ (m <: env)) o outb) mrho') (fn _ => raise Fail "Duplicated metavariables")
         val psi'' = raise Match
       in
         term <: (mrho'', rho, psi'') || stk
       end

     | O.MONO O.AP $ [_ \ m, _ \ n] <: env || stk =>
       m <: env || APP (HOLE, n) <: env :: stk
     | O.MONO O.LAM $ [(_, [x]) \ mx] <: (mrho, rho, psi) || APP (HOLE, n) <: env' :: stk =>
       mx <: (mrho, Var.Ctx.insert rho x (n <: env'), psi) || stk

     | _ => ?todo

  fun step sign stability (tm <: env || stk) =
    stepView sign stability (out tm <: env || stk)
end