signature MINI_SIGNATURE =
sig
  type metavar = RedPrlAbt.metavariable
  type symbol = RedPrlAbt.symbol
  type opid = RedPrlAbt.symbol
  type abt = RedPrlAbt.abt
  type valence = RedPrlAbt.valence
  type sort = RedPrlAbt.sort
  type psort = RedPrlAbt.psort
  type src_opid = string

  type 'a arguments = ('a * valence) list
  type 'a params = ('a * psort) list

  type sign
  type entry = {sourceOpid : src_opid, params : symbol params, arguments : metavar arguments, sort : sort, definiens : abt}

  val lookup : sign -> opid -> entry
end

signature SIGNATURE =
sig
  type ast = RedPrlAst.ast

  include MINI_SIGNATURE

  datatype src_decl =
     DEF of {arguments : string arguments, params : string params, sort : sort, definiens : ast}
   | THM of {arguments : string arguments, params : string params, goal : ast, script : ast}
   | TAC of {arguments : string arguments, params : string params, script : ast}

  datatype 'opid cmd =
     PRINT of 'opid

  type src_cmd = src_opid cmd

  val empty : sign
  val insert : sign -> src_opid -> src_decl * Pos.t option -> sign
  val command : sign -> src_opid cmd * Pos.t -> sign

  val check : sign -> bool
  val toString : sign -> string
end
