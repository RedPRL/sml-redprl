signature MINI_SIGNATURE =
sig
  type metavar = RedPrlAbt.metavariable
  type symbol = RedPrlAbt.symbol
  type opid = RedPrlAbt.symbol
  type abt = RedPrlAbt.abt
  type valence = RedPrlAbt.valence
  type sort = RedPrlAbt.sort
  type psort = RedPrlAbt.psort

  type 'a arguments = ('a * valence) list
  type 'a params = ('a * psort) list

  type sign
  type entry = {sourceOpid : string, params : symbol params, arguments : metavar arguments, sort : sort, definiens : abt}

  val lookup : sign -> opid -> entry
end

signature SIGNATURE =
sig
  type ast = RedPrlAst.ast

  include MINI_SIGNATURE

  datatype ast_decl =
     DEF of {arguments : string arguments, params : string params, sort : sort, definiens : ast}
   | THM of {arguments : string arguments, params : string params, goal : ast, script : ast}
   | TAC of {arguments : string arguments, params : string params, script : ast}

  val empty : sign
  val insert : sign -> string -> ast_decl * Pos.t option -> sign

  val check : sign -> bool
  val toString : sign -> string
end
