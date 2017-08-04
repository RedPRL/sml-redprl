structure Metalanguage : METALANGUAGE = 
struct
  structure Var = AbtSymbol ()
  structure Meta = AbtSymbol ()

  type mlvar = Var.t
  type meta = Meta.t

  val freshVar = Var.new

  structure Ctx : DICT = Var.Ctx

  datatype 'a mlscope = \ of mlvar * 'a
  infix \

  datatype mltype = 
     UNIT
   | ARR of mltype * mltype
   | PROD of mltype * mltype
   | OTERM of Tm.sort
   | META of meta

  type rule_name = string

  datatype mlterm = 
     VAR of mlvar
   | LET of mlterm * mlterm mlscope
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

  exception todo
  fun ?e = raise e
  
  fun unscope (_ \ _) =  ?todo
  fun mlscope _ = ?todo

  type octx = {metas: Tm.metactx, syms: Tm.symctx, vars: Tm.varctx}
  type mlctx = mlterm Ctx.dict

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