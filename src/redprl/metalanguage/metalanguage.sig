structure Tm = RedPrlAbt
structure Ast = RedPrlAst

signature METALANGUAGE = 
sig
  type mlvar
  type meta

  structure Ctx : DICT where type key = mlvar
  val freshVar : unit -> mlvar
  type ('v, 'a) mlscope

  datatype mltype = 
     UNIT
   | ARR of mltype * mltype
   | PROD of mltype * mltype
   | OTERM of Tm.sort
   | META of meta

  type rule_name = string

  datatype ('v, 'o) mlterm = 
     VAR of 'v
   | LET of ('v, 'o) mlterm * ('v, ('v, 'o) mlterm) mlscope
   | LAM of ('v, ('v, 'o) mlterm) mlscope
   | APP of ('v, 'o) mlterm * ('v, 'o) mlterm
   | PAIR of ('v, 'o) mlterm * ('v, 'o) mlterm
   | FST of ('v, 'o) mlterm
   | SND of ('v, 'o) mlterm
   | QUOTE of 'o | GOAL
   | REFINE of rule_name
   | EACH of ('v, 'o) mlterm list
   | NIL

  val unscope : (mlvar, (mlvar, 'o) mlterm) mlscope -> mlvar * (mlvar, 'o) mlterm
  val scope : mlvar * (mlvar, 'o) mlterm -> (mlvar, (mlvar, 'o) mlterm) mlscope
  val strScope : string * (string, 'o) mlterm -> (string, (string, 'o) mlterm) mlscope

  type mlterm_ = (mlvar, Tm.abt) mlterm
  val resolve : (string, Ast.ast * Tm.sort) mlterm -> mlterm_

  structure Statics :
  sig
    type octx = {metas: Tm.metactx, syms: Tm.symctx, vars: Tm.varctx}
    type mlctx = mlterm_ Ctx.dict
    datatype mode = LOCAL | GLOBAL
    val infer : mode -> octx -> mlctx -> mlterm_ -> mltype
    val check : mode -> octx -> mlctx -> mlterm_ -> mltype -> unit
  end
end
