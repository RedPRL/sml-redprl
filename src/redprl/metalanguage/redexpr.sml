structure RedExpr : REDEXPR = 
struct
  type annotation = Pos.t option

  type 'a ident = 'a * annotation

  datatype 'a expr = 
     IDENT of 'a ident
   | NUMERAL of int
   | BINDING of 'a ident list * annotation
   | TYPED_BINDING of 'a ident list * 'a expr * annotation
   | GROUP of 'a expr list * annotation

  type 'a forest = 'a expr list

  fun @@ (f, x) = f x
  infixr @@

  local
    structure ML = MetalanguageSyntax
    structure MLR = ML.Resolver
    structure Tm = RedPrlAbt
    structure Names = StringListDict

    open RedPrlAst Tm
    structure O = RedPrlOpData

    exception todo
    infix $ $$ $# \
    fun ?e = raise e
  in
    type abt = abt
    type state =
      {metactx: Tm.metactx,
       varctx: Tm.varctx,
       symctx : Tm.symctx,
       metaenv: Tm.metavariable Names.dict,
       symenv: Tm.symbol Names.dict,
       varenv: Tm.variable Names.dict}

    datatype head = 
       OPERATOR of Tm.operator
     | METAVAR of Tm.metavariable * valence
     | TERM of Tm.abt

    fun lookupVarName (state : state) a : Tm.variable * sort = 
      let
        val a' = Names.lookup (#varenv state) a
        val tau = Var.Ctx.lookup (#varctx state) a'
      in
        (a', tau)
      end

    fun lookupMetavarName (state : state) a : Tm.metavariable * valence = 
      let
        val a' = Names.lookup (#metaenv state) a
        val vl = Metavar.Ctx.lookup (#metactx state) a'
      in
        (a', vl)
      end

    fun readVarTerm (state : state) a = 
      let
        val (a', tau) = lookupVarName state a
      in
        check (`a', tau)
      end

    type stack = string expr list

    fun bindSymbols {metactx,varctx,symctx,metaenv,symenv,varenv} (idents : string ident list, sorts) : symbol list * state =
      let
        val xs = List.map #1 idents
        val xs' = List.map Sym.named xs
        val symenv' = ListPair.foldl (fn (x,x',rho) => Names.insert rho x x') symenv (xs, xs')
        val symctx' = ListPair.foldl (fn (x,sigma,rho) => Sym.Ctx.insert rho x sigma) symctx (xs', sorts)
      in
        (xs', {metactx = metactx, varctx = varctx, symctx = symctx', metaenv = metaenv, varenv = varenv, symenv = symenv'})
      end

    fun bindVars {metactx,varctx,symctx,metaenv,symenv,varenv} (idents : string ident list, sorts) : variable list * state =
      let
        val xs = List.map #1 idents
        val xs' = List.map Var.named xs
        val varenv' = ListPair.foldl (fn (x,x',rho) => Names.insert rho x x') varenv (xs, xs')
        val varctx' = ListPair.foldl (fn (x,tau,rho) => Var.Ctx.insert rho x tau) varctx (xs', sorts)
      in
        (xs', {metactx = metactx, varctx = varctx', symctx = symctx, metaenv = metaenv, varenv = varenv', symenv = symenv})
      end

    fun readHead (state : state) (rexpr, stk : stack) : head * stack =
      case rexpr of 
          IDENT (a, pos) => readIdentHead state (a, stk)
        | GROUP (hd :: rexprs, _) => readHead state (hd, rexprs @ stk)
        | _ => raise Fail "Syntax error"

    and readIdentHead (state : state) (a, stk) : head * stack = 
      (TERM (readVarTerm state a) handle _ => METAVAR (lookupMetavarName state a), stk)
      handle _ => 
        let
          val (theta, stk) = readOperator state (a, stk)
        in
          (OPERATOR theta, stk)
        end

    and readOperator state (opname, stk) : Tm.operator * stack =
      case opname of
         "bool" => (O.MONO O.BOOL, stk)
       | "wbool" => (O.MONO O.WBOOL, stk)
       | "dfun" => (O.MONO O.DFUN, stk)
       | _ => raise Fail "unknown operator"

    and readParam (state : state) (rexpr, sigma) : Tm.param =
      case rexpr of 
         IDENT (a, _) => Tm.O.P.VAR (Names.lookup (#symenv state) a)
       | NUMERAL 0 => Tm.O.P.APP RedPrlParamData.DIM0
       | NUMERAL 1 => Tm.O.P.APP RedPrlParamData.DIM1
       | _ => raise Fail "unknown parameter"

    and plugHead (state : state) (hd : head, stk : stack) = 
      case hd of 
         OPERATOR theta =>
         let
           val (vls, tau) = Tm.O.arity theta
           val (args, []) = readOpArgs state (vls, stk) []
           val term = check (theta $ args, tau)
         in
           term
         end
       | METAVAR (a, ((psorts, sorts), tau)) =>
         let
           val (params, stk) = readParams state (psorts, stk) []
           val (args, stk) = readMetaArgs state (sorts, stk) []
           val term = check (a $# (params, args), tau)
         in
           plugTerm state (term, stk)
         end
       | TERM e => plugTerm state (e, stk)

    and readParams (state : state) (psorts, stk : stack) memo : (param * psort) list * stack =
      case (psorts, stk) of
         ([], _) => (List.rev memo, stk)
       | (sigma :: psorts, r :: stk) => readParams state (psorts, stk) ((readParam state (r, sigma), sigma) :: memo)

    and readMetaArgs (state : state) (sorts, stk : stack) memo : abt list * stack = 
      case (sorts, stk) of 
         ([], _) => (List.rev memo, stk)
       | (tau :: sorts, e :: stk) => readMetaArgs state (sorts, stk) (reader state e :: memo)

    and readOpArgs (state : state) (vls, stk : stack) memo : abt bview list * stack =
      case (vls, stk) of 
         ([], _) => (List.rev memo, stk)
       | (vl :: vls, stk) => 
         let
           val (binder, stk) = readBinderArg state (vl, stk)
         in
           readOpArgs state (vls, stk) (binder :: memo)
         end

    and readBinderArg (state : state) (valence, stk : stack) : abt bview * stack =
      case (valence, stk) of 
         ((([],[]), _), e::stk) => (([],[]) \ reader state e, stk)
       | (((ssorts, []), _), BINDING (us, _) :: e :: stk) =>
         let
           val (us', state) = bindSymbols state (us, ssorts)
           val binder = (us', []) \ reader state e
         in
           (binder, stk)
         end
       | ((([], vsorts), _), BINDING (xs, _) :: e :: stk) =>
         let
           val (xs', state) = bindVars state (xs, vsorts)
           val binder = ([], xs') \ reader state e
         in
           (binder, stk)
         end
       | (((ssorts, vsorts), _), BINDING (us, _) :: BINDING (xs, _) :: e :: stk) =>
         let
           val (us', state) = bindSymbols state (us, ssorts)
           val (xs', state) = bindVars state (xs, vsorts)
           val binder = (us', xs') \ reader state e
         in
           (binder, stk)
         end

    and plugTerm (state : state) (e : abt, stk : stack) =
      case stk of 
         [] => e
       | rexpr :: stk => plugTerm state (O.MONO O.APP $$ [([],[]) \ e, ([],[]) \ reader state rexpr], stk)

    and reader state rexpr =
      plugHead state @@
        readHead state (rexpr, [])
  end
end