structure MlExtSyntax = 
struct
  type sort = RedPrlSort.t
  type valence = RedPrlAbt.valence

  type id = MlId.t
  type metavariable = string
  type jdg = RedPrlAst.ast
  type term = RedPrlAst.ast * sort
  type vty = MlType.vty

  type metas = (metavariable * valence) list
  type arguments = (metavariable * valence) list

  datatype cmd =
     DEF of {arguments : arguments, definiens : term}
   | THM of {name : string, arguments : arguments, goal : jdg, script : RedPrlAst.ast}
   | TAC of {arguments : arguments, script : RedPrlAst.ast}

   | PRINT_EXTRACT of Pos.t option * value
   | EXTRACT of value
   | NU of metas * cmd

   | BIND of cmd * id * cmd
   | RET of value
   | FORCE of value
   | FN of id * vty * cmd
   | AP of cmd * value
   | PRINT of Pos.t option * value
   | REFINE of string option * jdg * RedPrlAst.ast
   | FRESH of (string option * valence) list
   | MATCH_METAS of value * metavariable list * cmd
   | MATCH_ABS of value * id * id * cmd
   | MATCH_THM of value * id * id * cmd
   | ABORT

  and value =
     THUNK of cmd
   | VAR of id
   | NIL
   | ABS of value * value
   | METAS of metas
   | TERM of term
end

structure MlIntSyntax = 
struct
  type id = MlId.t
  type valence = RedPrlAbt.valence
  type metavariable = RedPrlAbt.metavariable
  type jdg = AtomicJudgment.jdg
  type term = RedPrlAbt.abt
  type vty = MlType.vty

  type metas = (metavariable * valence) list

  datatype value =
     THUNK of cmd
   | VAR of id
   | NIL
   | ABS of value * value
   | METAS of metas
   | TERM of term

  and cmd =
     BIND of cmd * id * cmd
   | RET of value
   | FORCE of value
   | FN of id * vty * cmd
   | AP of cmd * value
   | PRINT of Pos.t option * value
   | REFINE of string option * jdg * term
   | FRESH of (string option * valence) list
   | MATCH_METAS of value * metavariable list * cmd
   | MATCH_ABS of value * id * id * cmd
   | MATCH_THM of value * id * id * cmd
   | ABORT
end