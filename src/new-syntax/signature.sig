signature MINI_SIGNATURE =
sig
  type opid = RedPrlAbt.symbol
  type abt = RedPrlAbt.abt
  type valence = RedPrlAbt.valence
  type sort = RedPrlAbt.sort
  type arguments = (string * valence) list

  type sign
  type entry = {sourceOpid : string, arguments : arguments, sort : sort, definiens : abt}

  val lookup : sign -> opid -> entry
end

signature SIGNATURE =
sig
  type ast = RedPrlAst.ast

  include MINI_SIGNATURE

  datatype ast_decl =
     DEF of {arguments : arguments, sort : sort, definiens : ast}
   | THM of {arguments : arguments, goal : ast, script : ast}
   | TAC of {arguments : arguments, script : ast}

  val empty : sign
  val insert : sign -> string -> ast_decl * Pos.t option -> sign

  val check : sign -> unit
  val toString : sign -> string
end
