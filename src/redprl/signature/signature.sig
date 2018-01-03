signature SIGNATURE = 
sig
  type sort
  type valence
  type ast
  type abt
  type metavariable
  type ajdg


  (* source language: to be phased out *)
  structure Src :
  sig
    type arguments = (string * valence) list

    datatype decl =
       DEF of {arguments : arguments, sort : sort, definiens : ast}
     | THM of {arguments : arguments, goal : ast, script : ast}
     | TAC of {arguments : arguments, script : ast}

    datatype cmd =
       PRINT of string
     | EXTRACT of string
     | QUIT

    datatype elt = 
       DECL of string * decl * Pos.t
     | CMD of cmd * Pos.t

    type sign = elt list
  end

  structure Ty : ML_TYPE
  structure ESyn : ML_SYNTAX (* before name resolution *)
  structure ISyn : ML_SYNTAX (* after name resolution *)

  (* semantic domain *)
  structure Sem : 
  sig
    type value
    type cmd
    type env

    val ppValue : value -> Fpp.doc
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
