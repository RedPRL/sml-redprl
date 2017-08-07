structure Tm = RedPrlAbt
structure Ast = RedPrlAst

signature METALANGUAGE = 
sig
  type mlvar
  type meta

  structure Ctx : DICT where type key = mlvar
  val freshVar : unit -> mlvar
  type ('b, 'a) scope

  datatype mltype = 
     UNIT
   | ARR of mltype * mltype
   | PROD of mltype * mltype
   | OTERM of Tm.sort
   | META of meta

  type rule_name = string

  datatype ('v, 's, 'o) mlterm = 
     VAR of 'v
   | LET of ('v, 's, 'o) mlterm * ('v, ('v, 's, 'o) mlterm) scope
   | LAM of ('v, ('v, 's, 'o) mlterm) scope
   | APP of ('v, 's, 'o) mlterm * ('v, 's, 'o) mlterm
   | PAIR of ('v, 's, 'o) mlterm * ('v, 's, 'o) mlterm
   | FST of ('v, 's, 'o) mlterm
   | SND of ('v, 's, 'o) mlterm
   | QUOTE of 'o | GOAL
   | REFINE of rule_name
   | EACH of ('v, 's, 'o) mlterm list
   | TRY of ('v, 's, 'o) mlterm * ('v, 's, 'o) mlterm
   | PUSH of ('s list, ('v, 's, 'o) mlterm) scope
   | NIL

  type mlterm_ = (mlvar, Tm.symbol, Tm.abt) mlterm

  val unscope : ('b, ('v, 's, 'o) mlterm) scope -> 'b * ('v, 's, 'o) mlterm
  val scope : mlvar * (mlvar, 's, 'o) mlterm -> (mlvar, (mlvar, 's, 'o) mlterm) scope
  val oscope : Tm.symbol list * ('v, Tm.symbol, Tm.abt) mlterm -> (Tm.symbol list, ('v, Tm.symbol, Tm.abt) mlterm) scope

  structure Resolver : 
  sig
    val strScope : string * (string, 's, 'o) mlterm -> (string, (string, 's, 'o) mlterm) scope
    val resolve : (string, string, Ast.ast * Tm.sort) mlterm -> mlterm_
  end

  structure Statics :
  sig
    type octx = {metas: Tm.metactx, syms: Tm.symctx, vars: Tm.varctx}
    type mlctx = mlterm_ Ctx.dict
    datatype mode = LOCAL | GLOBAL
    val infer : mode -> octx -> mlctx -> mlterm_ -> mltype
    val check : mode -> octx -> mlctx -> mlterm_ -> mltype -> unit
  end
end
