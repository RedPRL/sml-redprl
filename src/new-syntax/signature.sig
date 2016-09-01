signature AST_SIGNATURE =
sig

  type ast = RedPrlAst.ast
  type sort = RedPrlSort.t
  type metavariable = RedPrlAst.metavariable
  type valence = RedPrlArity.valence

  type arguments = (metavariable * valence) list

  datatype ast_decl =
     DEF of {arguments : arguments, sort : sort, definiens : ast}
   | THM of {arguments : arguments, goal : ast, script : ast}
   | TAC of {arguments : arguments, script : ast}

  (* A signature / [sign] is a telescope of declarations. *)
  type sign

  val empty : sign
  val insert : sign -> string -> ast_decl * Pos.t option -> sign

  val toString : sign -> string

end
