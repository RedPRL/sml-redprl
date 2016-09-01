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
end
