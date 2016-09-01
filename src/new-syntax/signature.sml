structure AstSignature :> AST_SIGNATURE =
struct
  type term = RedPrlAst.ast
  type symbol = RedPrlAst.symbol
  type sort = RedPrlSort.t
  type metavariable = RedPrlAst.metavariable
  type valence = RedPrlArity.valence

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  datatype decl =
     DEF of {arguments : arguments, sort : sort, definiens : term}
   | THM of {arguments : arguments, goal : term, script : term}
   | TAC of {arguments : arguments, script : term}

  type opid = RedPrlAst.symbol
  structure Telescope = Telescope (StringAbtSymbol)

  (* A signature / [sign] is a telescope of declarations. *)
  type sign = (decl * Pos.t option) Telescope.telescope

  val argsToString : arguments -> string =
    ListSpine.pretty (fn (x, vl) => "#" ^ x ^ " : " ^ RedPrlArity.Vl.toString vl) ","


  fun declToString (opid, decl) =
    case decl of
       DEF {arguments, sort, definiens} =>
         "Def " ^ opid ^ "(" ^ argsToString arguments ^ ") : " ^ RedPrlSort.toString sort ^ " = [" ^ RedPrlAst.toString definiens ^ "]."
     | THM {arguments, goal, script} =>
         "Def " ^ opid ^ "(" ^ argsToString arguments ^ ") : [" ^ RedPrlAst.toString goal ^ "] by [" ^ RedPrlAst.toString script ^ "]."
     | TAC {arguments, script} =>
         "Tac " ^ opid ^ "(" ^ argsToString arguments ^ ") = [" ^ RedPrlAst.toString script ^ "]."

  val arityOfDecl =
    fn DEF {arguments, sort, definiens} => (List.map #2 arguments, sort)
     | THM {arguments, goal, script} => (List.map #2 arguments, RedPrlOpData.THM)
     | TAC {arguments, script} => (List.map #2 arguments, RedPrlOpData.TAC)

  fun arityOfOpid (sign : sign) =
    Option.map (arityOfDecl o #1)
      o Telescope.find sign

  (* During parsing, the arity of a custom-operator application is not known; but we can
   * derive it from the signature "so far". Prior to adding a declaration to the signature,
   * we elaborate its terms to fill this in. TODO: think about how to deal with the case of
   * extending an existing signature that already passed through the binding/abt elaboration. *)
  local
    structure O = RedPrlOpData
    open RedPrlAst infix $ $$ $# $$# \

    fun elabOp sign =
      fn O.POLY (O.CUST (opid, NONE)) => O.POLY (O.CUST (opid, arityOfOpid sign opid))
       | th => th
  in
    fun elabTerm sign m =
      case out m of
         `x => ``x
       | th $ es => elabOp sign th $$ List.map (fn bs \ m => bs \ elabTerm sign m) es
       | x $# (ps, ms) => x $$# (ps, List.map (elabTerm sign) ms)
  end

  fun elabDecl sign =
    fn DEF {arguments, sort, definiens} => DEF {arguments = arguments, sort = sort, definiens = elabTerm sign definiens}
     | THM {arguments, goal, script} => THM {arguments = arguments, goal = elabTerm sign goal, script = elabTerm sign script}
     | TAC {arguments, script} => TAC {arguments = arguments, script = elabTerm sign script}

  val empty = Telescope.empty

  fun snoc sign opid (decl, pos) =
    Telescope.snoc sign opid (elabDecl sign decl, pos)

  fun toString sign =
    let
      open Telescope.ConsView
      fun go EMPTY = ""
        | go (CONS (opid, (decl, _), xs)) =
            declToString (opid, decl) ^ "\n\n" ^ go (out xs)
    in
      go (out sign)
    end
end
