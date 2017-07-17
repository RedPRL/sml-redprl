signature CLOSURE = 
sig
  type environment
  type param = RedPrlAbt.param
  type term = RedPrlAbt.abt
  type sort = RedPrlAbt.sort
  type psort = RedPrlAbt.psort
  type valence = RedPrlAbt.valence
  type 'a binder = 'a RedPrlAbt.bview

  datatype 'a closure = <: of 'a * environment

  val variable : (Var.t * sort) -> environment -> term closure
  val metavariable : (Metavar.t * (param * psort) list * term list * sort) -> environment -> term closure

  structure Env :
  sig
    type t = environment

    val empty : t
    val lookupSym : t -> Sym.t -> param
    val forceParam : t -> param -> param
    val forceTerm  : t -> term -> term

    val insertMeta : Metavar.t -> term closure binder -> t -> t
    val insertVar : Var.t -> term closure -> t -> t
    val insertSym : Sym.t -> param -> t -> t
  end
end
