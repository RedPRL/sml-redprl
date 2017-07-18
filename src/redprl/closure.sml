structure Closure :> CLOSURE = 
struct
  structure Tm = RedPrlAbt and P = RedPrlParameterTerm
  type param = Tm.param
  type term = Tm.abt
  type sort = Tm.sort
  type psort = Tm.psort
  type valence = Tm.valence
  type 'a binder = 'a Tm.bview


  (* A 'shallow env' contains a substitution of terms for variables, and parameters for symbols. *)

  type shallow_env =
    {vars: Tm.abt Var.Ctx.dict,
     syms: Tm.param Sym.Ctx.dict}
  
  (* A 'final env' is a list of shallow env; this is a "formal composition" of environments.
     Unlike in the document, the implementation uses one of these lists everwhere, rather than only
     in the definition of forcing. We may wish to change this, I have no idea. *)
  type final_env = shallow_env list

  datatype 'a closure = <: of 'a * environment
  and environment = ** of deep_env * final_env
  withtype deep_env = 
    {metas: Tm.abt closure Tm.bview Metavar.Ctx.dict,
     vars: Tm.abt closure Var.Ctx.dict,
     syms: Tm.param Sym.Ctx.dict}


  infix 3 <:
  infix 4 **

  structure Env = 
  struct
    type t = environment
    local
      val emptyDeep = {metas = Metavar.Ctx.empty, vars = Var.Ctx.empty, syms = Sym.Ctx.empty}
    in
      val empty =
        emptyDeep ** []
    end

    local
      fun lookupSymDeep (E : deep_env) u = 
        Sym.Ctx.lookup (#syms E) u 
        handle Sym.Ctx.Absent => 
          P.ret u

      fun lookupSymShallow (F : shallow_env) u = 
        Sym.Ctx.lookup (#syms F) u 
        handle Sym.Ctx.Absent => 
          P.ret u

      (* Favonia: is this correct? To get the value of a symbol from the list of final substitutions,
         do we have to walk through the whole list and apply all possible substitutions? *)
      fun lookupSymFinal L u = 
        case L of 
           [] => P.ret u
         | F :: L => P.bind (lookupSymFinal L) (lookupSymShallow F u)
    in
      (* First, lookup the symbol in E; then, apply whatever substitutions are in L. *)
      fun lookupSym (E ** L) u =
        P.bind (lookupSymFinal L) (lookupSymDeep E u)
    end

    fun forceParam (E ** L) = 
      P.bind (lookupSym (E ** L))


    local
      open Tm infix $ $$ $# \
    in
      (* These two functions implement E+(x). *)
      fun lookupMeta (E : deep_env) x = 
        Metavar.Ctx.lookup (#metas E) x
        (*TODO: handle Absent  *)

      fun lookupVar (E : deep_env) (x, tau) =
        Var.Ctx.lookup (#vars E) x
        handle Var.Ctx.Absent => 
          check (`x, tau)
            <: E ** []

      fun lookupVarFinal (F : shallow_env) (x, tau) = 
        Var.Ctx.lookup (#vars F) x 
        handle Var.Ctx.Absent => 
          check (`x, tau)

      fun forceVarFinal L (x, tau) = 
        forceTermFinal L (check (`x, tau))

      and forceTermFinal L tm = 
        case L of 
           [] => tm
         | F :: L => forceTermFinal L (forceTermShallow F tm)
      
      and forceTermShallow F = 
        substSymenv (#syms F)
          o substVarenv (#vars F)

      and forceTerm (E ** L) tm =
        case infer tm of 
           (`x, tau) => 
             (case Var.Ctx.find (#vars E) x of 
                 SOME (m <: E' ** L') => forceTerm (E' ** (L' @ L)) m
               | NONE => forceVarFinal L (x, tau))
         | (x $# (rs, ms), tau) => 
             (case Metavar.Ctx.find (#metas E) x of 
                 SOME ((us, xs) \ n <: E' ** L') =>
                 let
                   val F = 
                     {vars = ListPair.foldr (fn (x, m, rho) => Var.Ctx.insert rho x (forceTerm (E ** L) m)) Var.Ctx.empty (xs, ms),
                      syms = ListPair.foldr (fn (u, (r, _), rho) => Sym.Ctx.insert rho u (forceParam (E ** L) r)) Sym.Ctx.empty (us, rs)}
                 in
                   forceTerm (E' ** (L' @ F :: L)) n
                 end
               | NONE => 
                 let
                   val rs' = List.map (fn (r, sigma) => (forceParam (E ** L) r, sigma)) rs
                   val ms' = List.map (fn m => forceTerm (E ** L) m) ms
                 in
                   check (x $# (rs', ms'), tau)
                 end)
         | (theta $ args, _) =>
           let
             val theta' = O.map (lookupSym (E ** L)) theta
             val args' = List.map (fn (us, xs) \ n => (us, xs) \ forceTerm (E ** L) n) args
           in
             theta' $$ args'
           end
    end

    fun insertMeta x bndCl ({metas, vars, syms} ** L) =
      {metas = Metavar.Ctx.insert metas x bndCl, vars = vars, syms = syms} 
        ** L

    fun insertVar x cl ({metas, vars, syms} ** L) = 
      {metas = metas, vars = Var.Ctx.insert vars x cl, syms = syms}
        ** L

    fun insertSym u r ({metas, vars, syms} ** L) = 
      {metas = metas, vars = vars, syms = Sym.Ctx.insert syms u r}
        ** L
  end

  local
    open Tm infix $# \
  in
    fun variable (x, tau) (E ** L) = 
      let
        val m <: E' ** L' = Env.lookupVar E (x, tau)
      in
        m <: E' ** (L' @ L)
      end

    fun metavariable (x, rs, ms, tau) (E ** L) =
      let
        val (us, xs) \ n <: E' ** L' = Env.lookupMeta E x
        val F =
          {vars = ListPair.foldrEq (fn (x, m, rho) => Var.Ctx.insert rho x (Env.forceTerm (E ** L) m)) Var.Ctx.empty (xs, ms),
           syms = ListPair.foldrEq (fn (u, (r, _), rho) => Sym.Ctx.insert rho u (Env.forceParam (E ** L) r)) Sym.Ctx.empty (us, rs)}
        val L'' = L @ [F]
      in
        n <: E' ** (L' @ L'')
      end
  end
end
