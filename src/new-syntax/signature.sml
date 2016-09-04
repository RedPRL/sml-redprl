structure Signature :> SIGNATURE =
struct
  structure E = ElabMonadUtil (ElabMonad)
  structure ElabNotation = MonadNotation (E)
  open ElabNotation infix >>= *>

  structure MiniSig =
  struct
    type abt = RedPrlAbt.abt
    type ast = RedPrlAst.ast
    type sort = RedPrlSort.t
    type valence = RedPrlArity.valence
    type opid = RedPrlAbt.symbol

    type arguments = (string * valence) list
    type entry = {sourceOpid : string, arguments : arguments, sort : sort, definiens : abt}

    datatype ast_decl =
       DEF of {arguments : arguments, sort : sort, definiens : ast}
     | THM of {arguments : arguments, goal : ast, script : ast}
     | TAC of {arguments : arguments, script : ast}

    (* elaborated declarations *)
    datatype elab_decl = EDEF of entry

    structure Telescope = Telescope (StringAbtSymbol)
    structure ETelescope = Telescope (RedPrlAbt.Sym)
    structure NameEnv = AstToAbt.NameEnv

    (* A signature / [sign] is a telescope of declarations. *)
    type ast_sign = (ast_decl * Pos.t option) Telescope.telescope

    (* An elaborated signature is a telescope of definitions. *)
    type elab_sign = elab_decl E.t ETelescope.telescope

    type sign =
      {sourceSign : ast_sign,
       elabSign : elab_sign,
       nameEnv : RedPrlAbt.symbol NameEnv.dict}

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
    val arityOfDecl =
      fn DEF {arguments, sort, definiens} => (List.map #2 arguments, sort)
       | THM {arguments, goal, script} => (List.map #2 arguments, O.THM)
       | TAC {arguments, script} => (List.map #2 arguments, O.TAC)

    fun arityOfOpid (sign : ast_sign) =
      Option.map (arityOfDecl o #1)
        o Telescope.find sign

    (* During parsing, the arity of a custom-operator application is not known; but we can
     * derive it from the signature "so far". Prior to adding a declaration to the signature,
     * we process its terms to fill this in. *)
    local
      open RedPrlAst
      infix $ $$ $# $$# \

      fun processOp sign =
        fn O.POLY (O.CUST (opid, NONE)) => O.POLY (O.CUST (opid, arityOfOpid sign opid))
         | th => th
      fun processTerm sign m =
        case out m of
           `x => ``x
         | th $ es => processOp sign th $$ List.map (fn bs \ m => bs \ processTerm sign m) es
         | x $# (ps, ms) => x $$# (ps, List.map (processTerm sign) ms)
    in
      fun processDecl sign =
        fn DEF {arguments, sort, definiens} => DEF {arguments = arguments, sort = sort, definiens = processTerm sign definiens}
         | THM {arguments, goal, script} => THM {arguments = arguments, goal = processTerm sign goal, script = processTerm sign script}
         | TAC {arguments, script} => TAC {arguments = arguments, script = processTerm sign script}
    end

    structure MetaCtx = RedPrlAbt.Metavar.Ctx
    structure Seq = RedPrlSequent

    structure LcfModel = LcfModel (MiniSig)
    structure Refiner = NominalLcfSemantics (LcfModel)

    fun metactxFromArguments args =
      List.foldl
        (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl)
        MetaCtx.empty
        args

    fun elabDef ({nameEnv,...} : sign) opid {arguments, sort, definiens} =
      E.ret () >>= (fn _ =>
        let
          val metactx = metactxFromArguments arguments
          val definiens' = AstToAbt.convertOpen metactx (nameEnv, NameEnv.empty) (definiens, sort)
        in
          E.ret (EDEF {sourceOpid = opid, arguments = arguments, sort = sort, definiens = definiens'})
        end)

    fun elabThm sign opid pos {arguments, goal, script} =
      E.ret () >>= (fn _ =>
        let
          open Seq RedPrlAbt RedPrlOpData infix >> \
          val metactx = metactxFromArguments arguments
          val goal' = AstToAbt.convertOpen metactx (#nameEnv sign, NameEnv.empty) (goal, JDG)
          val script' = AstToAbt.convertOpen metactx (#nameEnv sign, NameEnv.empty) (script, TAC)
          val judgment = Hyps.empty >> CJ.fromAbt goal'
          val names = fn i => Sym.named ("@" ^ Int.toString i)
          val state as (subgoals, vld) = Refiner.tactic (sign, Var.Ctx.empty) script' names judgment

          local
            open RedPrlAbt infix $$ \
          in
            val elabDefiniens =
              if LcfModel.Lcf.T.isEmpty subgoals then
                let
                  val _ \ evd = outb (vld (LcfModel.Lcf.T.empty))
                in
                  E.ret (MONO (REFINE true) $$ [([],[]) \ goal', ([],[]) \ script', ([],[]) \ evd])
                end
              else
                let
                  val stateStr = LcfModel.Lcf.stateToString state
                in
                  E.warn (pos, "Refinement failed: \n\n" ^ stateStr)
                    *> (E.ret (MONO (REFINE false) $$ [([],[]) \ goal', ([],[]) \ script']))
                end
          end
        in
          elabDefiniens >>= (fn definiens =>
            E.ret (EDEF {sourceOpid = opid, arguments = arguments, sort = THM, definiens = definiens}))
        end)

    fun elabTac ({nameEnv,...} : sign) opid {arguments, script} =
      E.ret () >>= (fn _ =>
        let
          val metactx = List.foldl (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl) MetaCtx.empty arguments
          val script' = AstToAbt.convertOpen metactx (nameEnv, NameEnv.empty) (script, O.TAC)
        in
          E.ret (EDEF {sourceOpid = opid, arguments = arguments, sort = O.TAC, definiens = script'})
        end)

    fun elabDecl (sign : sign) (opid, eopid) (decl : ast_decl, pos) : elab_sign =
      let
        val esign' = ETelescope.truncateFrom (#elabSign sign) eopid
        val sign' = {sourceSign = #sourceSign sign, elabSign = esign', nameEnv = #nameEnv sign}
        fun decorate e = e >>= (fn x => E.info (pos, declToString (opid, decl)) *> E.ret x)
      in
        case processDecl (#sourceSign sign) decl of
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

        val eopid = RedPrlAbt.Sym.named opid
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
    in
      pos' ^ ": " ^ msg ^"\n\n"
    end

  val checkAlg : (elab_decl, unit) E.alg =
    {warn = fn (msg, _) => TextIO.output (TextIO.stdErr, formatMessage msg),
     info = fn (msg, _) => TextIO.output (TextIO.stdOut, formatMessage msg),
     init = (),
     succeed = fn _ => (),
     fail = fn (msg, _) => TextIO.output (TextIO.stdErr, formatMessage msg)}

  fun check ({elabSign,...} : sign) =
    ETelescope.foldl (fn (e, _) => E.fold checkAlg e) () elabSign
end
