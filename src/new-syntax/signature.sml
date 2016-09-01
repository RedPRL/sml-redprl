structure AstSignature : AST_SIGNATURE =
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
