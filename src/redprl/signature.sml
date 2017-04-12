structure Signature :> SIGNATURE =
struct
  structure Tm = RedPrlAbt
  structure P = RedPrlParamData
  structure E = ElabMonadUtil (ElabMonad)
  structure ElabNotation = MonadNotation (E)
  open ElabNotation infix >>= *> <*

  fun @@ (f, x) = f x
  infixr @@

  open MiniSig
  structure O = RedPrlOpData and E = ElabMonadUtil (ElabMonad)

  local
    open PP

    fun argsToString f =
      ListSpine.pretty (fn (x, vl) => "#" ^ f x ^ " : " ^ RedPrlArity.Vl.toString vl) ", "
      
    fun paramsToString f =
      ListSpine.pretty (fn (x, vl) => f x ^ " : " ^ RedPrlArity.Vl.PS.toString vl) ", "

    val kwd = color C.red o bold true
    val declId = blink true o underline true

    fun delim (l,r) x =
      concat
        [color C.white @@ text l,
         x,
         color C.white @@ text r]

    val squares = delim ("[", "]")
    val braces = delim ("{", "}")
    val parens = delim ("(", ")")
  in
    fun prettyDecl (opid, decl) =
      case decl of
         DEF {arguments, params, sort, definiens} =>
           concat
             [kwd @@ text "Def ", declId @@ text opid, 
              braces @@ text @@ paramsToString (fn x => x) params,
              parens @@ text @@ argsToString (fn x => x) arguments, text " : ",
              text @@ RedPrlSort.toString sort, text " = ",
              squares @@ concat [nest 2 @@ concat [line, text (RedPrlAst.toString definiens)], line],
              text "."]
       | THM {arguments, params, goal, script} =>
           concat
             [kwd @@ text "Thm ",
              declId @@ text opid,
              braces @@ text @@ paramsToString (fn x => x) params,
              parens @@ text @@ argsToString (fn x => x) arguments,
              text " : ",
              squares @@ concat [nest 2 @@ concat [line, text @@ RedPrlAst.toString goal], line],
              text " by ",
              squares @@ concat [nest 2 @@ concat [line, text @@ RedPrlAst.toString script], line],
              text "."]
       | TAC {arguments, params, script} =>
           concat
            [kwd @@ text "Tac ", declId @@ text opid,
             braces @@ text @@ paramsToString (fn x => x) params,
             parens @@ text @@ argsToString (fn x => x) arguments,
             text " = ",
             squares @@ concat [nest 2 @@ concat [line, text @@ RedPrlAst.toString script], line],
             text "."]


    val declToString =
      PP.toString 80 false o prettyDecl

    fun prettyEntry (sign : sign) (opid, {sourceOpid, params, arguments, sort, spec, state} : entry) =
      let
        val src = prettyDecl (sourceOpid, #1 (Telescope.lookup (#sourceSign sign) sourceOpid))
        val term = extract state
        val elab =
          concat
            [kwd @@ text "Def ",
             declId @@ text @@ Sym.toString opid,
             braces @@ text @@ paramsToString Sym.toString params,
             parens @@ text @@ argsToString Metavar.toString arguments,
             text " : ",
             text @@ RedPrlSort.toString sort, text " = ",
             squares @@ concat [nest 2 @@ concat [line, text @@ TermPrinter.toString term], line],
             text "."]
      in
        concat [src, newline, newline, text "===>", newline, newline, elab]
      end

    fun entryToString (sign : sign) =
      PP.toString 80 false o prettyEntry sign

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
    val getEntry =
      fn EDEF entry => SOME entry
       | _ => NONE

    fun arityOfDecl ({sourceOpid, arguments, params, sort, spec, state} : entry) : Tm.psort list * Tm.O.Ar.t =
      (List.map #2 params, (List.map #2 arguments, sort))

    structure OptionMonad = MonadNotation (OptionMonad)

    fun arityOfOpid (sign : sign) opid =
      let
        open OptionMonad infix >>=
      in
        NameEnv.find (#nameEnv sign) opid
          >>= ETelescope.find (#elabSign sign)
          >>= E.run
          >>= Option.map arityOfDecl o getEntry
      end

    structure Err = RedPrlError

    fun error pos msg = raise Err.annotate pos (Err.error msg)

    (* During parsing, the arity of a custom-operator application is not known; but we can
     * derive it from the signature "so far". Prior to adding a declaration to the signature,
     * we process its terms to fill this in. *)
    local
      open RedPrlAst
      infix $ $$ $# $$# \

      fun processOp pos sign =
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
             | NONE => error pos [Err.% "Encountered undefined custom operator:", Err.% opid])
         | th => th

      fun processTerm' sign m =
        case out m of
           `x => ``x
         | th $ es => processOp (getAnnotation m) sign th $$ List.map (fn bs \ m => bs \ processTerm sign m) es
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

    fun elabDeclArguments args =
      List.foldr
        (fn ((x, vl), (args', mctx)) =>
          let
            val x' = Metavar.named x
          in
            ((x', vl) :: args', MetaCtx.insert mctx x' vl)
          end)
        ([], MetaCtx.empty)
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
        val symOccurrences = Susp.delay (fn _ => Tm.symOccurrences term)
        val checkSyms =
          Tm.Sym.Ctx.foldl
            (fn (u, tau, r) =>
              let
                val tau' = Tm.Sym.Ctx.find symctx u
                val ustr = Tm.Sym.toString u
                val pos = case Tm.Sym.Ctx.find (Susp.force symOccurrences) u of
                               SOME (pos :: _) => SOME pos
                             | _ => (print ("couldn't find position for var " ^ ustr); termPos)
              in
                E.when (tau' = NONE, E.fail (pos, "Unbound symbol: " ^ ustr))
                  *> E.when (Option.isSome tau' andalso not (tau' = SOME tau), E.fail (pos, "Symbol sort mismatch: " ^ ustr))
                  *> r
              end)
            (E.ret ())
            (Tm.symctx term)

        val varOccurrences = Susp.delay (fn _ => Tm.varOccurrences term)
        val checkVars =
          Tm.Var.Ctx.foldl
            (fn (x, tau, r) =>
               let
                 val pos = case Tm.Var.Ctx.find (Susp.force varOccurrences) x of
                               SOME (pos :: _) => SOME pos
                             | _ => termPos
               in
                 E.fail (pos, "Unbound variable: " ^ Tm.Var.toString x) *> r
               end)
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

    fun metactxToNameEnv metactx =
      Tm.Metavar.Ctx.foldl
        (fn (x, _, r) => AstToAbt.NameEnv.insert r (Tm.Metavar.toString x) x)
        AstToAbt.NameEnv.empty
        metactx

    fun convertToAbt (metactx, symctx, env) ast sort =
      E.wrap (RedPrlAst.getAnnotation ast,
              fn () => AstToAbt.convertOpen (metactx, metactxToNameEnv metactx) (env, NameEnv.empty) (ast, sort)
                       handle AstToAbt.BadConversion (msg, pos) => error pos [Err.% msg])
        >>= scopeCheck (metactx, symctx)

    fun elabDef (sign : sign) opid {arguments, params, sort, definiens} =
      let
        val (arguments', metactx) = elabDeclArguments arguments
        val (params', symctx, env) = elabDeclParams sign params
      in
        convertToAbt (metactx, symctx, env) definiens sort >>= (fn definiens' =>
          let
            val tau = sort
            open RedPrlAbt infix \
            val state' = Lcf.|> (Lcf.Tl.empty, checkb (([],[]) \ definiens', (([],[]), tau)))
          in
            E.ret (EDEF {sourceOpid = opid, params = params', arguments = arguments', sort = tau, spec = NONE, state = state'})
          end)
      end

    fun <&> (m, n) = m >>= (fn x => n >>= (fn y => E.ret (x, y)))
    infix <&>

    local
      open RedPrlSequent Tm RedPrlOpData infix >> \ $$

      fun names i = Sym.named ("@" ^ Int.toString i)

      fun elabRefine sign (goal, seqjdg, script) =
        let
          val (_, tau) = RedPrlJudgment.sort seqjdg
          val pos = getAnnotation script
        in
          E.wrap (pos, fn _ => Refiner.tactic (sign, Var.Ctx.empty) script names seqjdg)
        end

      fun ensureCompleteState pos (state as Lcf.|> (subgoals, evidence)) = 
        if Lcf.Tl.isEmpty subgoals then
          E.ret ()
        else
          E.warn (pos, "Incomplete proof: \n\n" ^ Lcf.stateToString state)

      fun ensureCompleteDefinition pos decl =
        case decl of 
           EDEF {sourceOpid, params, arguments, sort, spec, state} => ensureCompleteState pos state *> E.ret decl
         | _ => E.ret decl
    in
      (* Foreshadowing the addition of support for derived rules, which will differ from theorems in that can have unsolved subgoals *)
      fun elabDerivedRule sign opid pos {arguments, params, goal, script} =
        let
          val (arguments', metactx) = elabDeclArguments arguments
          val (params', symctx, env) = elabDeclParams sign params
        in
          convertToAbt (metactx, symctx, env) goal SEQ >>= (fn goalTm =>
            let
              val seqjdg as hyps >> concl = RedPrlSequent.fromAbt goalTm
              val tau = CJ.synthesis concl
              val (params'', symctx', env') = 
                Hyps.foldr
                  (fn (x, jdg, (ps, ctx, env)) => 
                    ((x, RedPrlParamData.HYP) :: ps, Tm.Sym.Ctx.insert ctx x RedPrlParamData.HYP, NameEnv.insert env (Sym.toString x) x)) 
                  (params', symctx, env)
                  hyps
            in
              convertToAbt (metactx, symctx', env') script TAC 
                >>= (fn scriptTm => elabRefine sign (goalTm, seqjdg, scriptTm))
                >>= (fn state => E.ret @@ EDEF {sourceOpid = opid, params = params'', arguments = arguments', sort = tau, spec = SOME seqjdg, state = state})
            end)
        end

      fun elabThm sign opid pos thm = 
        elabDerivedRule sign opid pos thm
          >>= ensureCompleteDefinition pos 
    end

    fun elabTac (sign : sign) opid {arguments, params, script} =
      let
        val (arguments', metactx) = elabDeclArguments arguments
        val (params', symctx, env) = elabDeclParams sign params

      in
        convertToAbt (metactx, symctx, env) script O.TAC >>= (fn script' =>
          let
            open O RedPrlAbt infix \
            val state' = Lcf.|> (Lcf.Tl.empty, checkb (([],[]) \ script', (([],[]), TAC)))
          in
            E.ret @@ EDEF {sourceOpid = opid, params = params', arguments = arguments', sort = TAC, spec = NONE, state = state'}
          end)
      end

    fun elabDecl (sign : sign) (opid, eopid) (decl : src_decl, pos) : elab_sign =
      let
        val esign' = ETelescope.truncateFrom (#elabSign sign) eopid
        val sign' = {sourceSign = #sourceSign sign, elabSign = esign', nameEnv = #nameEnv sign}
        fun decorate e = e >>= (fn x => E.dump (pos, declToString (opid, decl)) *> E.ret x)
      in
        ETelescope.snoc esign' eopid (decorate (E.delay (fn _ =>
          case processDecl sign decl of
             DEF defn => elabDef sign' opid defn
           | THM defn => elabThm sign' opid pos defn
           | TAC defn => elabTac sign' opid defn)))
      end

    fun elabPrint (sign : sign) (pos, opid) =
      E.wrap (SOME pos, fn _ => NameEnv.lookup (#nameEnv sign) opid) >>= (fn eopid =>
        E.hush (ETelescope.lookup (#elabSign sign) eopid) >>= (fn edecl =>
          E.ret (ECMD (PRINT eopid)) <*
            (case edecl of
                EDEF entry => E.info (SOME pos, "Elaborated:\n" ^ entryToString sign (eopid, entry))
              | _ => E.warn (SOME pos, "Invalid declaration name"))))

    local
      open RedPrlAbt infix $ \
      structure O = RedPrlOpData

      fun printExtractOf (pos, state) : unit E.t = 
        E.info (SOME pos, TermPrinter.toString (extract state))
    in
      fun elabExtract (sign : sign) (pos, opid) = 
        E.wrap (SOME pos, fn _ => NameEnv.lookup (#nameEnv sign) opid) >>= (fn eopid => 
          E.hush (ETelescope.lookup (#elabSign sign) eopid) >>= (fn edecl => 
            E.ret (ECMD (EXTRACT eopid)) <*
              (case edecl of 
                  EDEF entry => printExtractOf (pos, #state entry)
                | _ => E.warn (SOME pos, "Invalid declaration name"))))
    end

    fun elabCmd (sign : sign) (cmd, pos) : elab_sign =
      case cmd of
         PRINT opid =>
           let
             val fresh = Sym.named "_"
           in
             ETelescope.snoc (#elabSign sign) fresh (E.delay (fn _ => elabPrint sign (pos, opid)))
           end
       | EXTRACT opid => 
           let
             val fresh = Sym.named "_"
           in
             ETelescope.snoc (#elabSign sign) fresh (E.delay (fn _ => elabExtract sign (pos, opid)))
           end


    fun insertAstDecl sign opid (decl, pos) =
      let
        val sign' = Telescope.truncateFrom sign opid
      in
        Telescope.snoc sign opid (decl, pos)
      end
      handle Telescope.Duplicate l => error pos [Err.% "Duplicate identitifier:", Err.% l]

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

    fun command (sign : sign) (cmd, pos) =
      let
        val elabSign = elabCmd sign (cmd, pos)
      in
        {sourceSign = #sourceSign sign, elabSign = elabSign, nameEnv = #nameEnv sign}
      end
  end

  structure L = RedPrlLog

  val checkAlg : (elab_decl, bool) E.alg =
    {warn = fn (msg, r) => (L.print L.WARN msg; false),
     info = fn (msg, r) => (L.print L.INFO msg; r),
     dump = fn (msg, r) => (L.print L.DUMP msg; r),
     init = true,
     succeed = fn (_, r) => r,
     fail = fn (msg, _) => (L.print L.FAIL msg; false)}

  fun check ({elabSign,...} : sign) =
    ETelescope.foldl (fn (_, e, r) => E.fold checkAlg e andalso r) true elabSign
end
