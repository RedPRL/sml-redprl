structure Signature :> SIGNATURE =
struct
  structure Tm = RedPrlAbt
  structure P = RedPrlParamData
  structure E = ElabMonadUtil (ElabMonad)
  structure ElabNotation = MonadNotation (E)
  open ElabNotation infix >>= *> <*

  fun @@ (f, x) = f x
  infixr @@

  structure MiniSig =
  struct
    type abt = Tm.abt
    type ast = RedPrlAst.ast
    type sort = RedPrlAbt.sort
    type psort = RedPrlAbt.psort
    type valence = RedPrlArity.valence
    type symbol = Tm.symbol
    type opid = Tm.symbol

    type 'a params = ('a * psort) list
    type arguments = (string * valence) list
    type entry = {sourceOpid : string, params : symbol params, arguments : arguments, sort : sort, definiens : abt}

    datatype ast_decl =
       DEF of {arguments : arguments, params : string params, sort : sort, definiens : ast}
     | THM of {arguments : arguments, params : string params, goal : ast, script : ast}
     | TAC of {arguments : arguments, params : string params, script : ast}

    (* elaborated declarations *)
    datatype elab_decl = EDEF of entry

    structure Telescope = Telescope (StringAbtSymbol)
    structure ETelescope = Telescope (Tm.Sym)
    structure NameEnv = AstToAbt.NameEnv

    (* A signature / [sign] is a telescope of declarations. *)
    type ast_sign = (ast_decl * Pos.t option) Telescope.telescope

    (* An elaborated signature is a telescope of definitions. *)
    type elab_sign = elab_decl E.t ETelescope.telescope

    type sign =
      {sourceSign : ast_sign,
       elabSign : elab_sign,
       nameEnv : Tm.symbol NameEnv.dict}

    fun lookup ({elabSign, ...} : sign) opid =
      case E.run (ETelescope.lookup elabSign opid) of
         SOME (EDEF defn) => defn
       | NONE => raise Fail "Elaboration failed"
  end

  open MiniSig
  structure O = RedPrlOpData

  local
    val argsToString : arguments -> string =
      ListSpine.pretty (fn (x, vl) => "#" ^ x ^ " : " ^ RedPrlArity.Vl.toString vl) ", "
  in
    fun declToString (opid, decl) =
      case decl of
         DEF {arguments, params, sort, definiens} =>
           "Def " ^ opid ^ "(" ^ argsToString arguments ^ ") : " ^ RedPrlSort.toString sort ^ " = [" ^ RedPrlAst.toString definiens ^ "]."
       | THM {arguments, params, goal, script} =>
           "Thm " ^ opid ^ "(" ^ argsToString arguments ^ ") : [" ^ RedPrlAst.toString goal ^ "] by [" ^ RedPrlAst.toString script ^ "]."
       | TAC {arguments, params, script} =>
           "Tac " ^ opid ^ "(" ^ argsToString arguments ^ ") = [" ^ RedPrlAst.toString script ^ "]."

    fun toString ({sourceSign,...} : sign) =
      let
        open Telescope.ConsView
        fun go EMPTY = ""
          | go (CONS (opid, (decl, _), xs)) =
              declToString (opid, decl) ^ "\n\n" ^ go (out xs)
      in
        go (out sourceSign)
      end
  end

  val empty =
    {sourceSign = Telescope.empty,
     elabSign = ETelescope.empty,
     nameEnv = NameEnv.empty}

  local
    fun arityOfDecl (EDEF {sourceOpid, arguments, params, sort, definiens}) : Tm.psort list * Tm.O.Ar.t=
      (List.map #2 params, (List.map #2 arguments, sort))

    structure OptionMonad = MonadNotation (OptionMonad)

    fun arityOfOpid (sign : sign) opid =
      let
        open OptionMonad infix >>=
      in
        NameEnv.find (#nameEnv sign) opid
          >>= ETelescope.find (#elabSign sign)
          >>= E.run
          >>= SOME o arityOfDecl
      end

    (* During parsing, the arity of a custom-operator application is not known; but we can
     * derive it from the signature "so far". Prior to adding a declaration to the signature,
     * we process its terms to fill this in. *)
    local
      open RedPrlAst
      infix $ $$ $# $$# \

      fun processOp sign =
        fn O.POLY (O.CUST (opid, ps, NONE)) =>
           (case arityOfOpid sign opid of
               SOME (psorts, ar) =>
                 let
                   val ps' =
                     ListPair.mapEq
                       (fn ((p, _), tau) =>
                          let
                            val _ = O.P.check tau p
                          in
                            (p, SOME tau)
                          end)
                       (ps, psorts)
                 in
                   O.POLY (O.CUST (opid, ps', SOME ar))
                 end
             | NONE => raise Fail "Encountered undefined custom operator")
         | th => th

      fun processTerm' sign m =
        case out m of
           `x => ``x
         | th $ es => processOp sign th $$ List.map (fn bs \ m => bs \ processTerm sign m) es
         | x $# (ps, ms) => x $$# (ps, List.map (processTerm sign) ms)

      and processTerm sign m =
        setAnnotation (getAnnotation m) (processTerm' sign m)
    in
      fun processDecl sign =
        fn DEF {arguments, params, sort, definiens} => DEF {arguments = arguments, params = params, sort = sort, definiens = processTerm sign definiens}
         | THM {arguments, params, goal, script} => THM {arguments = arguments, params = params, goal = processTerm sign goal, script = processTerm sign script}
         | TAC {arguments, params, script} => TAC {arguments = arguments, params = params, script = processTerm sign script}
    end

    structure MetaCtx = Tm.Metavar.Ctx

    structure LcfModel = LcfModel (MiniSig)
    structure Refiner = NominalLcfSemantics (LcfModel)

    fun metactxFromArguments args =
      List.foldl
        (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl)
        MetaCtx.empty
        args

    fun elabDeclParams (sign : sign) (params : string params) : symbol params * Tm.symctx * symbol NameEnv.dict =
      let
        val (ctx0, env0) =
          ETelescope.foldl
            (fn (x, _, (ctx, env)) => (Tm.Sym.Ctx.insert ctx x P.OPID, NameEnv.insert env (Tm.Sym.toString x) x))
            (Tm.Sym.Ctx.empty, NameEnv.empty)
            (#elabSign sign)
      in
        List.foldr
          (fn ((x, tau), (ps, ctx, env)) =>
            let
              val x' = Tm.Sym.named x
            in
              ((x', tau) :: ps, Tm.Sym.Ctx.insert ctx x' tau, NameEnv.insert env x x')
            end)
          ([], ctx0, env0)
          params
      end

    fun scopeCheck (metactx, symctx) term : Tm.abt E.t =
      let
        val termPos = Tm.getAnnotation term
        val checkSyms =
          Tm.Sym.Ctx.foldl
            (fn (u, tau, r) =>
              let
                val tau' = Tm.Sym.Ctx.find symctx u
                val ustr = Tm.Sym.toString u
              in
                E.when (tau' = NONE, E.fail (termPos, "Unbound symbol: " ^ ustr))
                  *> E.when (Option.isSome tau' andalso not (tau' = SOME tau), E.fail (termPos, "Symbol sort mismatch: " ^ ustr))
                  *> r
              end)
            (E.ret ())
            (Tm.symctx term)

        val checkVars =
          Tm.Var.Ctx.foldl
            (fn (x, tau, r) => E.fail (termPos, "Unbound variable: " ^ Tm.Var.toString x) *> r)
            (E.ret ())
            (Tm.varctx term)

        val checkMetas =
          Tm.Metavar.Ctx.foldl
            (fn (x, vl, r) =>
               r <* E.unless (Option.isSome (Tm.Metavar.Ctx.find metactx x), E.fail (termPos, "Unbound metavar: " ^ Tm.Metavar.toString x)))
            (E.ret ())
            (Tm.metactx term)
      in
        checkVars *> checkSyms *> checkMetas *> E.ret term
      end

    fun convertToAbt (metactx, symctx, env) ast sort =
      E.wrap (RedPrlAst.getAnnotation ast, fn () => AstToAbt.convertOpen metactx (env, NameEnv.empty) (ast, sort))
        >>= scopeCheck (metactx, symctx)

    fun elabDef (sign : sign) opid {arguments, params, sort, definiens} =
      let
        val metactx = metactxFromArguments arguments
        val (params', symctx, env) = elabDeclParams sign params
      in
        convertToAbt (metactx, symctx, env) definiens sort >>= (fn definiens' =>
          E.ret (EDEF {sourceOpid = opid, params = params', arguments = arguments, sort = sort, definiens = definiens'}))
      end

    fun <&> (m, n) = m >>= (fn x => n >>= (fn y => E.ret (x, y)))
    infix <&>

    local
      open RedPrlSequent Tm RedPrlOpData infix >> \ $$

      fun names i = Sym.named ("@" ^ Int.toString i)

      fun elabRefine sign (goal, script) =
        let
          val catjdg = CJ.fromAbt goal
          val seqjdg = Hyps.empty >> catjdg
          val tau = CJ.synthesis catjdg
          val pos = getAnnotation script
        in
          E.wrap (pos, fn _ => Refiner.tactic (sign, Var.Ctx.empty) script names seqjdg) >>= (fn state as (subgoals, vld) =>
            if LcfModel.Lcf.T.isEmpty subgoals then
              E.wrap (pos, fn _ => outb (vld (LcfModel.Lcf.T.empty))) >>= (fn _ \ evd =>
                 E.ret (MONO (REFINE (true, tau)) $$ [([],[]) \ goal, ([],[]) \ script, ([],[]) \ evd]))
            else
              let
                val stateStr = LcfModel.Lcf.stateToString state
              in
                E.warn (pos, "Refinement failed: \n\n" ^ stateStr)
                  *> (E.ret (MONO (REFINE (false, tau)) $$ [([],[]) \ goal, ([],[]) \ script]))
              end)
        end

    in
      fun elabThm sign opid pos {arguments, params, goal, script} =
        let
          val metactx = metactxFromArguments arguments
          val (params', symctx, env) = elabDeclParams sign params
          val names = fn i => Sym.named ("@" ^ Int.toString i)
        in
          convertToAbt (metactx, symctx, env) goal JDG <&> convertToAbt (metactx, symctx, env) script TAC
            >>= elabRefine sign
            >>= (fn definiens => E.ret @@ EDEF {sourceOpid = opid, params = params', arguments = arguments, sort = sort definiens, definiens = definiens})
        end
    end

    fun elabTac (sign : sign) opid {arguments, params, script} =
      let
        val metactx = metactxFromArguments arguments
        val (params', symctx, env) = elabDeclParams sign params
      in
        convertToAbt (metactx, symctx, env) script O.TAC >>= (fn script' =>
          E.ret @@ EDEF {sourceOpid = opid, params = params', arguments = arguments, sort = O.TAC, definiens = script'})
      end

    fun elabDecl (sign : sign) (opid, eopid) (decl : ast_decl, pos) : elab_sign =
      let
        val esign' = ETelescope.truncateFrom (#elabSign sign) eopid
        val sign' = {sourceSign = #sourceSign sign, elabSign = esign', nameEnv = #nameEnv sign}
        fun decorate e = e >>= (fn x => E.info (pos, declToString (opid, decl)) *> E.ret x)
      in
        case processDecl sign decl of
           DEF defn => ETelescope.snoc esign' eopid (decorate (E.delay (fn _ => elabDef sign' opid defn)))
         | THM defn => ETelescope.snoc esign' eopid (decorate (E.delay (fn _ => elabThm sign' opid pos defn)))
         | TAC defn => ETelescope.snoc esign' eopid (decorate (E.delay (fn _ => elabTac sign' opid defn)))
      end

    fun insertAstDecl sign opid (decl, pos) =
      let
        val sign' = Telescope.truncateFrom sign opid
      in
        Telescope.snoc sign opid (decl, pos)
      end

  in
    fun insert (sign : sign) opid (decl, pos) =
      let
        val sourceSign = insertAstDecl (#sourceSign sign) opid (decl, pos)

        val eopid = Tm.Sym.named opid
        val elabSign = elabDecl sign (opid, eopid) (decl, pos)
        val nameEnv = NameEnv.insert (#nameEnv sign) opid eopid
      in
        {sourceSign = sourceSign, elabSign = elabSign, nameEnv = nameEnv}
      end
  end

  structure L = RedPrlLog

  val checkAlg : (elab_decl, bool) E.alg =
    {warn = fn (msg, r) => (L.print L.WARN msg; false),
     info = fn (msg, r) => (L.print L.INFO msg; r),
     init = true,
     succeed = fn (_, r) => r,
     fail = fn (msg, _) => (L.print L.FAIL msg; false)}

  fun check ({elabSign,...} : sign) =
    ETelescope.foldl (fn (_, e, r) => E.fold checkAlg e andalso r) true elabSign
end
