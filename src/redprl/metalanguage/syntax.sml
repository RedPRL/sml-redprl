structure MetalanguageSyntax : METALANGUAGE_SYNTAX =
struct
  structure Var = AbtSymbol ()
  structure Meta = AbtSymbol ()

  structure Tm = RedPrlAbt and Ast = RedPrlAst
  type oast = Ast.ast
  type oterm = Tm.abt
  type osym = Tm.symbol
  type osort = Tm.sort
  type ovalence = Tm.valence

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

  type ('s, 'o, 't) omatch_clause = (('s * ovalence) list, 'o * 't) scope

  datatype ('v, 's, 'o, 'a) mltermf =
     VAR of 'v
   | LET of 'a * ('v, 'a) scope
   | FUN of ('v, 'a) scope
   | APP of 'a * 'a
   | PAIR of 'a * 'a
   | FST
   | SND
   | QUOTE of 'o | GOAL
   | REFINE of rule_name
   | EACH of 'a list
   | TRY of 'a * 'a
   | PUSH of ('s list, 'a) scope
   | NIL
   | PROVE of 'a * 'a
   | OMATCH of 'a * ('s, 'o, 'a) omatch_clause list
   | PRINT of 'a
   | EXACT of 'a

  type annotation = Pos.t option
  datatype ('v, 's, 'o) mlterm = :@ of ('v, 's, 'o, ('v, 's, 'o) mlterm) mltermf * annotation
  infix :@

  type mlterm_ = (mlvar, Tm.symbol, Tm.abt) mlterm
  type src_mlterm = (string, string, oast * osort) mlterm

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

    fun addMetas {ostate = {metactx, metaenv, symenv, varenv}, mlenv} metas metas' : state =
      {mlenv = mlenv,
       ostate = 
         {metactx = List.foldl (fn ((x, vl), r) => Tm.Metavar.Ctx.insert r x vl) metactx metas',
          metaenv = ListPair.foldl (fn ((x, _), (x', _), r) => Names.insert r x x') metaenv (metas, metas'),
          symenv = symenv,
          varenv = varenv}}

    fun mlvar (state : state) =
      Names.lookup (#mlenv state)

    fun resolveAbt {metactx, metaenv, symenv, varenv} oterm tau =
      A2A.convertOpen (metactx, metaenv) (symenv, varenv) (oterm, tau)

    fun resolveAux (state : state) : (string, string, Ast.ast * Tm.sort) mlterm -> mlterm_ =
      fn VAR x :@ ann => VAR (mlvar state x) :@ ann
       | LET (t, sc) :@ ann => LET (resolveAux state t, resolveAuxScope state sc) :@ ann
       | FUN sc :@ ann => FUN (resolveAuxScope state sc) :@ ann
       | APP (t1, t2) :@ ann => APP (resolveAux state t1, resolveAux state t2) :@ ann
       | PAIR (t1, t2) :@ ann => PAIR (resolveAux state t1, resolveAux state t2) :@ ann
       | FST :@ ann => FST :@ ann
       | SND :@ ann => SND :@ ann
       | QUOTE (ast, tau) :@ ann => QUOTE (resolveAbt (#ostate state) ast tau) :@ ann
       | GOAL :@ ann => GOAL :@ ann
       | REFINE ruleName :@ ann => REFINE ruleName :@ ann
       | EACH ts :@ ann => EACH (List.map (resolveAux state) ts) :@ ann
       | TRY (t1, t2) :@ ann => TRY (resolveAux state t1, resolveAux state t2) :@ ann
       | PUSH sc :@ ann => PUSH (resolveAuxObjScope state sc) :@ ann
       | NIL :@ ann => NIL :@ ann
       | PROVE (t1, t2) :@ ann => PROVE (resolveAux state t1, resolveAux state t2) :@ ann
       | OMATCH (scrutinee, clauses) :@ ann => OMATCH (resolveAux state scrutinee, List.map (resolveAuxObjMatchClause state) clauses) :@ ann
       | PRINT t :@ ann => PRINT (resolveAux state t) :@ ann
       | EXACT t :@ ann => EXACT (resolveAux state t) :@ ann

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

    and resolveAuxObjMatchClause (state : state) (metas \ ((pat, tau), t)) =
      let
        val metas' = List.map (fn (x, vl) => (Tm.Metavar.named x, vl)) metas
        val state' = addMetas state metas metas'
      in
        metas' \ (resolveAbt (#ostate state') pat tau, resolveAux state' t)
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

  structure Ast = 
  struct
    fun fn_ (x, t) pos : src_mlterm = 
      FUN (x \ t) :@ pos

    fun let_ (t, (x, tx)) pos = 
      LET (t, x \ tx) :@ pos

    fun push (xs : string list, t : src_mlterm) pos : src_mlterm = 
      PUSH (xs \ t) :@ pos
  end

end