signature SIGNATURE = 
sig
  type sort
  type ast

  structure Ty : ML_TYPE
  structure ESyn : ML_SYNTAX (* before name resolution *)
  structure ISyn : ML_SYNTAX (* after name resolution *)
  structure Sem : ML_SEMANTICS (* semantic domain *)

  sharing type Sem.jdg = ISyn.jdg
  sharing type Sem.term = ISyn.term
  sharing type Sem.syn_cmd = ISyn.cmd

  (* source language: to be phased out *)
  structure Src :
  sig
    type arguments = ESyn.metas

    datatype decl =
       DEF of {arguments : arguments, sort : sort, definiens : ast}
     | THM of {arguments : arguments, goal : ast, script : ast}
     | TAC of {arguments : arguments, script : ast}

    datatype cmd =
       PRINT of MlId.t
     | EXTRACT of MlId.t
     | QUIT

    datatype elt = 
       DECL of MlId.t * decl * Pos.t
     | CMD of cmd * Pos.t

    type sign = elt list
  end


  val compileSrcSig : Src.sign -> ESyn.cmd

  (* resolver *)
  structure Res : sig type env end
  val resolveCmd : Res.env -> ESyn.cmd -> ISyn.cmd * Ty.cty
  val resolveVal : Res.env -> ESyn.value -> ISyn.value * Ty.vty

  type exit_code = bool
  val evalCmd : Sem.env -> ISyn.cmd -> Sem.cmd * exit_code
  val evalVal : Sem.env -> ISyn.value -> Sem.value

  val checkSrcSig : Src.sign -> exit_code
end
