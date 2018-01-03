signature SIGNATURE = 
sig
  type sort
  type valence
  type ast
  type abt
  type metavariable
  type ajdg

  structure Ty : 
  sig
    datatype vty =
       ONE
     | DOWN of cty
     | TERM of sort
     | THM of sort
     | ABS of valence list * vty

    and cty = 
       UP of vty  
  end

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

  (* external language: before name resolution *)
  structure ESyn :
  sig
    datatype value = 
       THUNK of cmd
     | VAR of string
     | NIL
     | ABS of (string * valence) list * value
     | TERM of ast * sort

    and cmd = 
       BIND of cmd * string * cmd
     | RET of value
     | FORCE of value
     | PRINT of Pos.t option * value
     | REFINE of ast * ast
     | NU of (string * valence) list * cmd
     | ABORT
  end

  (* internal language *)
  structure ISyn :
  sig
    type value
    type cmd
  end

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

  val checkSrcSig : Src.sign -> bool
end
