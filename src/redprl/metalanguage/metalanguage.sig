structure Tm = RedPrlAbt

signature METALANGUAGE = 
sig
  type mlvar
  type meta

  structure Ctx : DICT where type key = mlvar
  val freshVar : unit -> mlvar

  type 'a mlscope

  datatype mltype = 
     UNIT
   | ARR of mltype * mltype
   | PROD of mltype * mltype
   | OTERM of Tm.sort
   | META of meta

  type rule_name = string

  datatype mlterm = 
     VAR of mlvar
   | LAM of mlterm mlscope
   | APP of mlterm * mlterm
   | PAIR of mlterm * mlterm
   | FST of mlterm
   | SND of mlterm
   | QUOTE of Tm.abt
   | REFINE of rule_name
   | ALL of mlterm
   | EACH of mlterm list
   | NIL

  val unscope : mlterm mlscope -> mlvar * mlterm
  val mlscope : mlvar * mlterm -> mlterm mlscope

  type octx = {metas: Tm.metactx, syms: Tm.symctx, vars: Tm.varctx}
  type mlctx = mlterm Ctx.dict

  datatype mode = LOCAL | GLOBAL

  val infer : mode -> octx -> mlctx -> mlterm -> mltype
  val check : mode -> octx -> mlctx -> mlterm -> mltype -> unit
end
