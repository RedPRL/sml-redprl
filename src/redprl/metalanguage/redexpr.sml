structure RedExpr : REDEXPR = 
struct
  type annotation = Pos.t option

  type 'a ident = 'a * annotation

  datatype 'a expr = 
     IDENT of 'a ident
   | NUMERAL of int * annotation
   | BINDING of 'a ident list * annotation
   | TYPED_BINDING of 'a ident list * 'a expr * annotation
   | GROUP of 'a forest * annotation

  withtype 'a forest = 'a expr list

  val getAnnotation = 
    fn IDENT (_, ann) => ann
     | NUMERAL (_, ann) => ann
     | BINDING (_, ann) => ann
     | TYPED_BINDING (_, _, ann) => ann
     | GROUP (_, ann) => ann

  fun @@ (f, x) = f x
  infixr @@

  local
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
       metaenv: Tm.metavariable Names.dict,
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

    fun bindVars {metactx,varctx,metaenv,varenv} (idents : string ident list, sorts) : variable list * state =
      let
        val xs = List.map #1 idents
        val xs' = List.map Var.named xs
        val varenv' = ListPair.foldl (fn (x,x',rho) => Names.insert rho x x') varenv (xs, xs')
        val varctx' = ListPair.foldl (fn (x,tau,rho) => Var.Ctx.insert rho x tau) varctx (xs', sorts)
      in
        (xs', {metactx = metactx, varctx = varctx', metaenv = metaenv, varenv = varenv'})
      end

    type stack = string expr list
    type sstack = stack list

    fun readHead (state : state) (rexpr, sstk : sstack) : head * sstack =
      case rexpr of 
          IDENT (a : string, pos) =>
          (case sstk of 
             stk :: sstk => let val (hd, stk') = readIdentHead state (a, stk) in (hd, stk' :: sstk) end
           | [] => let val (hd, _) = readIdentHead state (a, []) in (hd, []) end)
        | GROUP (hd :: rexprs, _) => readHead state (hd, rexprs :: sstk)
        | _ => raise Fail "Syntax error"

    and readIdentHead (state : state) (a, stk : stack) : head * stack = 
      (TERM (readVarTerm state a) handle _ => METAVAR (lookupMetavarName state a), stk)
      handle _ => 
        let
          val (theta, stk) = readOperator state (a, stk)
        in
          (OPERATOR theta, stk)
        end

    and readOperator state (opname, stk) : Tm.operator * stack =
      case opname of
         "bool" => (O.BOOL, stk)
       | "wbool" => (O.WBOOL, stk)
       | "fun" => (O.FUN, stk)
       | "tt" => (O.TT, stk)
       | "ff" => (O.FF, stk)
       | "path" => (O.PATH_TY, stk)
       | "loop" => (O.LOOP, stk)
       | "if" => (O.IF, stk)
       | _ => raise Fail "unknown operator"

    and plugHead (state : state) (hd : head, stk : stack) : abt = 
      case hd of 
         OPERATOR theta =>
         let
           val (vls, tau) = Tm.O.arity theta
           val (args, stk) = readOpArgs state (vls, stk) []
           val term = check (theta $ args, tau)
         in
           plugTerm state (term, stk)
         end
       | METAVAR (a, (sorts, tau)) =>
         let
           val (args, stk) = readMetaArgs state (sorts, stk) []
           val term = check (a $# args, tau)
         in
           plugTerm state (term, stk)
         end
       | TERM e => plugTerm state (e, stk)

    and plugHead' (state : state) (hd : head, sstk : sstack) = 
      case sstk of 
         [] => plugHead state (hd, [])
       | stk :: sstk => plugTerm' state (plugHead state (hd, stk), sstk)

    and plugTerm (state : state) (e : abt, stk : stack) : abt =
      case stk of 
         [] => e
       | rexpr :: stk => plugTerm state (O.APP $$ [[] \ e, [] \ reader state rexpr], stk)

    and plugTerm' (state : state) (e : abt, sstk : sstack) : abt =
      case sstk of
         [] => e
       | stk :: sstk => plugTerm' state (plugTerm state (e, stk), sstk)

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
         (([], _), e::stk) => ([] \ reader state e, stk)
       | ((vsorts, _), BINDING (xs, _) :: e :: stk) =>
         let
           val (xs', state) = bindVars state (xs, vsorts)
           val binder = xs' \ reader state e
         in
           (binder, stk)
         end

    and reader state rexpr =
      plugHead' state @@
        readHead state (rexpr, [])
  end
end