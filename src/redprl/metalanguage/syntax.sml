structure MetalanguageSyntax : METALANGUAGE_SYNTAX = 
struct
  structure Var = AbtSymbol ()
  structure Meta = AbtSymbol ()

  structure Tm = RedPrlAbt and Ast = RedPrlAst
  type oast = Ast.ast
  type oterm = Tm.abt
  type osym = Tm.symbol
  type osort = Tm.sort

  type mlvar = Var.t
  type meta = Meta.t

  val freshVar = Var.new

  structure Ctx : DICT = Var.Ctx

  datatype ('v, 'a) scope = \ of 'v * 'a
  infix \

  datatype mltype = 
     UNIT
   | ARR of mltype * mltype
   | PROD of mltype * mltype
   | OTERM of Tm.sort
   | THEOREM
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
   | PROVE of 'o * ('v, 's, 'o) mlterm 

  type mlterm_ = (mlvar, Tm.symbol, Tm.abt) mlterm

  exception todo
  fun ?e = raise e
  
  (* TODO: freshen *)
  fun unscope (x \ t) = (x, t)
  fun scope (x, t) = x \ t
  fun oscope (us, tm) = us \ tm

  structure Resolver = 
  struct
    structure A2A = AstToAbt
    structure Names = A2A.NameEnv

    fun scope (x, t) = x \ t

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
      
    fun addSyms {ostate = {metactx, metaenv, symenv, varenv}, mlenv} xs xs' : state = 
      {mlenv = mlenv,
       ostate = 
         {metactx = metactx,
          metaenv = metaenv,
          symenv = ListPair.foldl (fn (x, x', r) => Names.insert r x x') symenv (xs, xs'),
          varenv = varenv}}

    fun mlvar (state : state) = 
      Names.lookup (#mlenv state)

    fun resolveAbt {metactx, metaenv, symenv, varenv} oterm tau = 
      A2A.convertOpen (metactx, metaenv) (symenv, varenv) (oterm, tau)

    fun resolveAux (state : state) : (string, string, Ast.ast * Tm.sort) mlterm -> mlterm_ =
      fn VAR x => VAR (mlvar state x)
       | LET (t, sc) => LET (resolveAux state t, resolveAuxScope state sc)
       | LAM sc => LAM (resolveAuxScope state sc)
       | APP (t1, t2) => APP (resolveAux state t1, resolveAux state t2)
       | PAIR (t1, t2) => PAIR (resolveAux state t1, resolveAux state t2)
       | FST t => FST (resolveAux state t)
       | SND t => SND (resolveAux state t)
       | QUOTE (ast, tau) => QUOTE (resolveAbt (#ostate state) ast tau)
       | GOAL => GOAL
       | REFINE ruleName => REFINE ruleName
       | EACH ts => EACH (List.map (resolveAux state) ts)
       | TRY (t1, t2) => TRY (resolveAux state t1, resolveAux state t2)
       | PUSH sc => PUSH (resolveAuxObjScope state sc)
       | NIL => NIL
       | PROVE ((ast, tau), t) => PROVE (resolveAbt (#ostate state) ast tau, resolveAux state t)

    and resolveAuxScope (state : state) (x \ tx) = 
      let
        val x' = Var.named x
        val state' = addMlvar state x x'
      in
        x' \ resolveAux state' tx
      end

    and resolveAuxObjScope (state : state) (xs \ txs) =
      let
        val xs' = List.map Tm.Sym.named xs
        val state' = addSyms state xs xs'
      in
        xs' \ resolveAux state' txs
      end

    val resolve : (string, string, Ast.ast * Tm.sort) mlterm -> mlterm_ =
      resolveAux
        {ostate = 
          {metactx = Tm.Metavar.Ctx.empty,
           metaenv = Names.empty,
           symenv = Names.empty,
           varenv = Names.empty},
        mlenv = Names.empty}
    end
end