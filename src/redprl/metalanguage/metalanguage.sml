structure Metalanguage : METALANGUAGE = 
struct
  structure Var = AbtSymbol ()
  structure Meta = AbtSymbol ()

  type mlvar = Var.t
  type meta = Meta.t

  val freshVar = Var.new

  structure Ctx : DICT = Var.Ctx

  datatype ('v, 'a) mlscope = \ of 'v * 'a
  infix \

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
   | QUOTE of 'o
   | REFINE of rule_name
   | ALL of ('v, 'o) mlterm
   | EACH of ('v, 'o) mlterm list
   | NIL

  type mlterm_ = (mlvar, Tm.abt) mlterm

  exception todo
  fun ?e = raise e
  
  fun unscope (_ \ _) =  ?todo
  fun scope _ = ?todo
  fun strScope (x, t) = x \ t

  fun resolve _ = ?todo

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