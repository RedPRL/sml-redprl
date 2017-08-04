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
  
  (* TODO: freshen *)
  fun unscope (x \ t) = (x, t)
  fun scope (x, t) = x \ t
  fun strScope (x, t) = x \ t

  local
    structure A2A = AstToAbt
    structure Names = A2A.NameEnv

    type ostate =
      {metactx: Tm.metactx,
       metaenv: Tm.metavariable Names.dict,
       symenv: Tm.symbol Names.dict,
       varenv: Tm.variable Names.dict}

    type state = 
      {ostate: ostate,
       mlenv: mlvar Names.dict}
    
    fun addMlvar {ostate, mlenv} x x' = 
      {ostate = ostate,
       mlenv = Names.insert mlenv x x'}

    fun mlvar (state : state) = 
      Names.lookup (#mlenv state)

    fun resolveAbt {metactx, metaenv, symenv, varenv} oterm tau = 
      A2A.convertOpen (metactx, metaenv) (symenv, varenv) (oterm, tau)

    fun resolveAux (state : state) =
      fn VAR x => VAR (mlvar state x)
       | LET (t, sc) => LET (resolveAux state t, resolveAuxScope state sc)
       | LAM sc => LAM (resolveAuxScope state sc)
       | APP (t1, t2) => APP (resolveAux state t1, resolveAux state t2)
       | PAIR (t1, t2) => PAIR (resolveAux state t1, resolveAux state t2)
       | FST t => FST (resolveAux state t)
       | SND t => SND (resolveAux state t)
       | QUOTE (ast, tau) => QUOTE (resolveAbt (#ostate state) ast tau)
       | REFINE ruleName => REFINE ruleName
       | ALL t => ALL (resolveAux state t)
       | EACH ts => EACH (List.map (resolveAux state) ts)
       | NIL => NIL

    and resolveAuxScope (state : state) (x \ tx) = 
      let
        val x' = Var.named x
        val state' = addMlvar state x x'
      in
        x' \ resolveAux state' tx
      end
  in
    val resolve =
      resolveAux
        {ostate = 
          {metactx = Tm.Metavar.Ctx.empty,
           metaenv = Names.empty,
           symenv = Names.empty,
           varenv = Names.empty},
         mlenv = Names.empty}
  end

  structure Statics =
  struct
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
end