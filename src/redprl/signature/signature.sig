signature MINI_SIGNATURE =
sig
  type opid = RedPrlOpData.opid
  type abt = RedPrlAbt.abt
  
  type sign
  val opidSpec : sign -> opid -> abt RedPrlAbt.bview list -> AtomicJudgment.jdg
  val unfoldOpid : sign -> opid -> abt RedPrlAbt.bview list -> abt
end

signature SIGNATURE =
sig
  type ast = RedPrlAst.ast
  type metavar = RedPrlAbt.metavariable  
  type valence = RedPrlAbt.valence
  type sort = RedPrlAbt.sort
  type variable = RedPrlAbt.variable
  type src_opid = string
  type jdg = RedPrlJudgment.jdg
  

  include MINI_SIGNATURE

  type src_catjdg = ast
  type 'a arguments = ('a * valence) list
  

  datatype src_decl =
     DEF of {arguments : string arguments, sort : sort, definiens : ast}
   | THM of {arguments : string arguments, goal : src_catjdg, script : ast}
   | TAC of {arguments : string arguments, script : ast}

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
