signature METALANGUAGE_STATICS_KIT = 
sig
  include METALANGUAGE_SYNTAX
    where type oterm = RedPrlAbt.abt
    where type osym = RedPrlAbt.variable
end


functor Statics (ML : METALANGUAGE_STATICS_KIT) : METALANGUAGE_STATICS =
struct
  structure ML = ML and Tm = RedPrlAbt
  open ML

  exception todo
  fun ?e = raise e

  type octx = {metas: Tm.metactx, vars: Tm.varctx}
  type mlctx = mlterm_ Ctx.dict

  fun mltypeEq (mltype1, mltype2) = ?todo
  fun infer octx mlctx mlterm = ?todo

  fun check octx mlctx mlterm mltype = 
    let
      val mltype' = infer octx mlctx mlterm mltype
    in
      if mltypeEq (mltype, mltype') then
        ()
      else
        raise Fail "Type error"
    end
end