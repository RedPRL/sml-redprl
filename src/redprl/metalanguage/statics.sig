signature METALANGUAGE_STATICS = 
sig
  include METALANGUAGE

  type octx = {metas: RedPrlAbt.metactx, syms: RedPrlAbt.symctx, vars: RedPrlAbt.varctx}
  type mlctx = mlterm_ Ctx.dict
  datatype mode = LOCAL | GLOBAL
  val infer : mode -> octx -> mlctx -> mlterm_ -> mltype
  val check : mode -> octx -> mlctx -> mlterm_ -> mltype -> unit
end