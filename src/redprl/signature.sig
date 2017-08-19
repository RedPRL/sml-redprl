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
  type jdg = RedPrlJudgment.jdg

  type 'a arguments = ('a * valence) list
  type 'a params = ('a * psort) list
  type names = int -> symbol

  type sign
  type entry =
    {sourceOpid : src_opid,
     spec : jdg,
     state : names -> Lcf.jdg Lcf.state}

  val lookup : sign -> opid -> entry

  val entryParams : entry -> symbol params

  val applyCustomOperator : entry -> RedPrlAbt.param list -> abt RedPrlAbt.bview list -> RedPrlAbt.metaenv * RedPrlAbt.symenv
  val extract : Lcf.jdg Lcf.state -> abt
end

signature SIGNATURE =
sig
  type ast = RedPrlAst.ast

  include MINI_SIGNATURE

  type src_catjdg = RedPrlCategoricalJudgment.astjdg
  type src_seqhyp = string * src_catjdg
  type src_sequent = src_seqhyp list * src_catjdg

  datatype src_decl =
     DEF of {arguments : string arguments, params : string params, sort : sort, definiens : ast}
   | THM of {arguments : string arguments, params : string params, goal : src_sequent, script : ast}
   | TAC of {arguments : string arguments, params : string params, script : ast}

  datatype 'opid cmd =
     PRINT of 'opid
   | EXTRACT of 'opid

  type src_cmd = src_opid cmd

  datatype src_elt =
     DECL of string * src_decl * Pos.t
   | CMD of src_cmd * Pos.t

  val empty : sign
  val insert : sign -> src_opid -> src_decl * Pos.t option -> sign
  val command : sign -> src_opid cmd * Pos.t -> sign

  val check : sign -> bool
end
