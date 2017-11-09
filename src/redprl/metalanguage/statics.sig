signature METALANGUAGE_STATICS = 
sig
  structure ML : METALANGUAGE_SYNTAX

  type octx = {metas: RedPrlAbt.metactx, vars: RedPrlAbt.varctx}
  type mlctx = ML.mlterm_ ML.Ctx.dict
  val infer : octx -> mlctx -> ML.mlterm_ -> ML.mltype
  val check : octx -> mlctx -> ML.mlterm_ -> ML.mltype -> unit
end