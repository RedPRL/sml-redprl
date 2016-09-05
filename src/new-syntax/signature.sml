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
    type sort = RedPrlSort.t
    type valence = RedPrlArity.valence
    type opid = Tm.symbol

    type arguments = (string * valence) list
    type entry = {sourceOpid : string, arguments : arguments, sort : sort, definiens : abt}

    datatype ast_decl =
       DEF of {arguments : arguments, sort : sort, definiens : ast}
     | THM of {arguments : arguments, goal : ast, script : ast}
     | TAC of {arguments : arguments, script : ast}

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
         DEF {arguments, sort, definiens} =>
           "Def " ^ opid ^ "(" ^ argsToString arguments ^ ") : " ^ RedPrlSort.toString sort ^ " = [" ^ RedPrlAst.toString definiens ^ "]."
       | THM {arguments, goal, script} =>
           "Thm " ^ opid ^ "(" ^ argsToString arguments ^ ") : [" ^ RedPrlAst.toString goal ^ "] by [" ^ RedPrlAst.toString script ^ "]."
       | TAC {arguments, script} =>
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
    fun arityOfDecl (EDEF {sourceOpid, arguments, sort, definiens}) =
      (List.map #2 arguments, sort)

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
        fn O.POLY (O.CUST (opid, NONE)) => O.POLY (O.CUST (opid, arityOfOpid sign opid))
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
        fn DEF {arguments, sort, definiens} => DEF {arguments = arguments, sort = sort, definiens = processTerm sign definiens}
         | THM {arguments, goal, script} => THM {arguments = arguments, goal = processTerm sign goal, script = processTerm sign script}
         | TAC {arguments, script} => TAC {arguments = arguments, script = processTerm sign script}
    end

    structure MetaCtx = Tm.Metavar.Ctx

    structure LcfModel = LcfModel (MiniSig)
    structure Refiner = NominalLcfSemantics (LcfModel)

    fun metactxFromArguments args =
      List.foldl
        (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl)
        MetaCtx.empty
        args

    fun scopeCheck (sign : sign) metactx term : unit E.t =
      let
        val termPos = Tm.getAnnotation term
        val checkSyms =
          Tm.Sym.Ctx.foldl
            (fn (u, tau, r) =>
              E.unless
                (tau = P.OPID andalso Option.isSome (ETelescope.find (#elabSign sign) u),
                 E.warn (termPos, "Unbound symbol: " ^ Tm.Sym.toString u))
              *> r)
            (E.ret ())
            (Tm.symctx term)

        val checkVars =
          Tm.Var.Ctx.foldl
            (fn (x, tau, r) => E.warn (termPos, "Unbound variable: " ^ Tm.Var.toString x) *> r)
            (E.ret ())
            (Tm.varctx term)

        val checkMetas =
          Tm.Metavar.Ctx.foldl
            (fn (x, vl, r) =>
               r <*
                 (case Tm.Metavar.Ctx.find metactx x of
                     SOME vl' => E.unless (Tm.O.Ar.Vl.eq (vl, vl'), E.warn (termPos, "Metavar valence mismatch: " ^ Tm.Metavar.toString x))
                   | NONE => E.warn (termPos, "Unbound metavar: " ^ Tm.Metavar.toString x)))
            (E.ret ())
            (Tm.metactx term)
      in
        checkVars *> checkSyms *> checkMetas
      end

    fun elabDef (sign : sign) opid {arguments, sort, definiens} =
      E.ret () >>= (fn _ =>
        let
          val metactx = metactxFromArguments arguments
          val definiens' = AstToAbt.convertOpen metactx (#nameEnv sign, NameEnv.empty) (definiens, sort)
        in
          scopeCheck sign metactx definiens'
            *> E.ret (EDEF {sourceOpid = opid, arguments = arguments, sort = sort, definiens = definiens'})
        end)

    fun elabThm sign opid pos {arguments, goal, script} =
      E.ret () >>= (fn _ =>
        let
          open RedPrlSequent Tm RedPrlOpData infix >> \
          val metactx = metactxFromArguments arguments
          val goal' = AstToAbt.convertOpen metactx (#nameEnv sign, NameEnv.empty) (goal, JDG)
          val script' = AstToAbt.convertOpen metactx (#nameEnv sign, NameEnv.empty) (script, TAC)

          val catjdg = CJ.fromAbt goal'
          val seqjdg = Hyps.empty >> catjdg
          val sort = CJ.synthesis catjdg
          val names = fn i => Sym.named ("@" ^ Int.toString i)

          val elabProofState =
            E.ret (Refiner.tactic (sign, Var.Ctx.empty) script' names seqjdg)
              handle exn => E.fail (pos, exnMessage exn)

          val tau = CJ.synthesis catjdg

          local
            open Tm infix $$ \
          in
            val elabDefiniens =
              elabProofState >>= (fn state as (subgoals, vld) =>
                if LcfModel.Lcf.T.isEmpty subgoals then
                  (E.ret (outb (vld (LcfModel.Lcf.T.empty))) handle exn => E.fail (pos, exnMessage exn)) >>= (fn _ \ evd =>
                    E.ret (MONO (REFINE (true, tau)) $$ [([],[]) \ goal', ([],[]) \ script', ([],[]) \ evd]))
                else
                  let
                    val stateStr = LcfModel.Lcf.stateToString state
                  in
                    E.warn (pos, "Refinement failed: \n\n" ^ stateStr)
                      *> (E.ret (MONO (REFINE (false, tau)) $$ [([],[]) \ goal', ([],[]) \ script']))
                  end)
          end
        in
          scopeCheck sign metactx goal' *>
          scopeCheck sign metactx script' *>
          elabDefiniens >>= (fn definiens =>
            E.ret @@ EDEF {sourceOpid = opid, arguments = arguments, sort = THM sort, definiens = definiens})
        end)

    fun elabTac (sign : sign) opid {arguments, script} =
      E.ret () >>= (fn _ =>
        let
          val metactx = metactxFromArguments arguments
          val script' = AstToAbt.convertOpen metactx (#nameEnv sign, NameEnv.empty) (script, O.TAC)
        in
          scopeCheck sign metactx script'
            *> E.ret (EDEF {sourceOpid = opid, arguments = arguments, sort = O.TAC, definiens = script'})
        end)

    fun elabDecl (sign : sign) (opid, eopid) (decl : ast_decl, pos) : elab_sign =
      let
        val esign' = ETelescope.truncateFrom (#elabSign sign) eopid
        val sign' = {sourceSign = #sourceSign sign, elabSign = esign', nameEnv = #nameEnv sign}
        fun decorate e = e >>= (fn x => E.info (pos, declToString (opid, decl)) *> E.ret x)
      in
        case processDecl sign decl of
           DEF defn => ETelescope.snoc esign' eopid (decorate (elabDef sign' opid defn))
         | THM defn => ETelescope.snoc esign' eopid (decorate (elabThm sign' opid pos defn))
         | TAC defn => ETelescope.snoc esign' eopid (decorate (elabTac sign' opid defn))
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

  fun formatMessage (pos, msg) =
    let
      val pos' =
        case pos of
           SOME pos => Pos.toString pos
         | NONE => "[Unknown Location]"

      val lines = String.tokens (fn c => c = #"\n") msg
      val indented = List.map (fn l => "  " ^ l ^ "\n") lines
      val msg' = List.foldr op^ "" indented
    in
      pos' ^ ":\n" ^ msg' ^"\n\n"
    end

  val checkAlg : (elab_decl, unit) E.alg =
    {warn = fn (msg, _) => TextIO.output (TextIO.stdErr, formatMessage msg),
     info = fn (msg, _) => TextIO.output (TextIO.stdOut, formatMessage msg),
     init = (),
     succeed = fn _ => (),
     fail = fn (msg, _) => TextIO.output (TextIO.stdErr, formatMessage msg)}

  fun check ({elabSign,...} : sign) =
    ETelescope.foldl (fn (_, e, _) => E.fold checkAlg e) () elabSign
end
