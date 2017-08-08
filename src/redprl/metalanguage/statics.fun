signature METALANGUAGE_STATICS_KIT = 
sig
  include METALANGUAGE
    where type osort = RedPrlAbt.sort
    where type oterm = RedPrlAbt.abt
    where type osym = RedPrlAbt.symbol
end


functor Statics (ML : METALANGUAGE_STATICS_KIT) : METALANGUAGE_STATICS =
struct
  structure Tm = RedPrlAbt
  open ML

  exception todo
  fun ?e = raise e

  type octx = {metas: Tm.metactx, syms: Tm.symctx, vars: Tm.varctx}
  type mlctx = mlterm_ Ctx.dict

  datatype mode = LOCAL | GLOBAL
  fun mltypeEq (mltype1, mltype2) = ?todo
  fun infer mode octx mlctx mlterm = ?todo

  fun check mode octx mlctx mlterm mltype = 
    let
      val mltype' = infer mode octx mlctx mlterm mltype
    in
      if mltypeEq (mltype, mltype') then
        ()
      else
        raise Fail "Type error"
    end
end