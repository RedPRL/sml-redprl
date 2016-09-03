structure Signature :> SIGNATURE =
struct
  type abt = RedPrlAbt.abt
  type ast = RedPrlAst.ast
  type symbol = RedPrlAst.symbol
  type sort = RedPrlSort.t
  type metavariable = RedPrlAst.metavariable
  type valence = RedPrlArity.valence

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  structure O = RedPrlOpData

  datatype ast_decl =
     DEF of {arguments : arguments, sort : sort, definiens : ast}
   | THM of {arguments : arguments, goal : ast, script : ast}
   | TAC of {arguments : arguments, script : ast}

  (* elaborated declarations *)
  datatype elab_decl =
     EDEF of {sourceOpid : symbol, arguments : arguments, sort : sort, definiens : abt}

  type opid = RedPrlAst.symbol
  structure Telescope = Telescope (StringAbtSymbol)
  structure ETelescope = Telescope (RedPrlAbt.Sym)
  structure NameEnv = AstToAbt.NameEnv

  (* A signature / [sign] is a telescope of declarations. *)
  type ast_sign = (ast_decl * Pos.t option) Telescope.telescope

  (* An elaborated signature is a telescope of definitions. *)
  type elab_sign = elab_decl Susp.susp ETelescope.telescope

  type sign = ast_sign * elab_sign * RedPrlAbt.symbol NameEnv.dict

  local
    val argsToString : arguments -> string =
      ListSpine.pretty (fn (x, vl) => "#" ^ x ^ " : " ^ RedPrlArity.Vl.toString vl) ", "

    fun declToString (opid, decl) =
      case decl of
         DEF {arguments, sort, definiens} =>
           "Def " ^ opid ^ "(" ^ argsToString arguments ^ ") : " ^ RedPrlSort.toString sort ^ " = [" ^ RedPrlAst.toString definiens ^ "]."
       | THM {arguments, goal, script} =>
           "Thm " ^ opid ^ "(" ^ argsToString arguments ^ ") : [" ^ RedPrlAst.toString goal ^ "] by [" ^ RedPrlAst.toString script ^ "]."
       | TAC {arguments, script} =>
           "Tac " ^ opid ^ "(" ^ argsToString arguments ^ ") = [" ^ RedPrlAst.toString script ^ "]."
  in
    fun toString (sign, _, _) =
      let
        open Telescope.ConsView
        fun go EMPTY = ""
          | go (CONS (opid, (decl, _), xs)) =
              declToString (opid, decl) ^ "\n\n" ^ go (out xs)
      in
        go (out sign)
      end
  end

  val empty = (Telescope.empty, ETelescope.empty, NameEnv.empty)

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
     * we process its terms to fill this in. TODO: think about how to deal with the case of
     * extending an existing signature that already passed through the binding/abt elaboration. *)
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

    fun elabDef nameEnv opid {arguments, sort, definiens} =
      let
        val metactx = List.foldl (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl) MetaCtx.empty arguments
        val definiens' = AstToAbt.convertOpen metactx (nameEnv, NameEnv.empty) (definiens, sort)
      in
        EDEF
        {sourceOpid = opid,
         arguments = arguments,
         sort = sort,
         definiens = definiens'}
      end

    fun elabThm nameEnv opid {arguments, goal, script} =
      let
        val metactx = List.foldl (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl) MetaCtx.empty arguments
        val goal' = AstToAbt.convertOpen metactx (nameEnv, NameEnv.empty) (goal, O.EXP)
        val script' = AstToAbt.convertOpen metactx (nameEnv, NameEnv.empty) (script, O.TAC)

        local
          open RedPrlAbt infix $$ \
        in
          val definiens = RedPrlOpData.MONO (RedPrlOpData.REFINE false) $$ [([],[]) \ goal', ([],[]) \ script']
        end
      in
        EDEF
        {sourceOpid = opid,
         arguments = arguments,
         sort = O.THM,
         definiens = definiens}
      end


    fun elabTac nameEnv opid {arguments, script} =
      let
        val metactx = List.foldl (fn ((x, vl), mctx) => MetaCtx.insert mctx x vl) MetaCtx.empty arguments
        val script' = AstToAbt.convertOpen metactx (nameEnv, NameEnv.empty) (script, O.TAC)
      in
        EDEF
        {sourceOpid = opid,
         arguments = arguments,
         sort = O.TAC,
         definiens = script'}
      end

    fun elabDecl (sign, esign, nameEnv) (opid, eopid) (decl : ast_decl) : elab_sign =
      let
        val esign' = ETelescope.truncateFrom esign eopid
      in
        case processDecl sign decl of
           DEF defn => ETelescope.snoc esign' eopid (Susp.delay (fn () => elabDef nameEnv opid defn))
         | THM defn => ETelescope.snoc esign' eopid (Susp.delay (fn () => elabThm nameEnv opid defn))
         | TAC defn => ETelescope.snoc esign' eopid (Susp.delay (fn () => elabTac nameEnv opid defn))
      end

    fun insertAstDecl sign opid (decl, pos) =
      let
        val sign' = Telescope.truncateFrom sign opid
      in
        Telescope.snoc sign opid (decl, pos)
      end

  in
    fun insert (sign, esign, nameEnv) opid (decl, pos) =
      let
        val sign' = insertAstDecl sign opid (decl, pos)

        val eopid = RedPrlAbt.Sym.named opid
        val esign' = elabDecl (sign, esign, nameEnv) (opid, eopid) decl
        val nameEnv' = NameEnv.insert nameEnv opid eopid
      in
        (sign', esign', nameEnv')
      end
  end

  fun check (sign, esign, _) =
    ETelescope.foldl (fn (decl, _) => (Susp.force decl ; ())) () esign

end
