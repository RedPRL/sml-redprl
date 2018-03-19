structure MlExtSyntax = 
struct
  type id = MlId.t
  type metavariable = string
  type jdg = RedPrlAst.ast
  type term = RedPrlAst.ast * Tm.sort
  type vty = MlType.vty

  type metas = (metavariable * Tm.valence) list
  type arguments = (metavariable * Tm.valence) list
  type sort = Tm.sort

  datatype cmd =
     DEF of {arguments : arguments, sort : sort, definiens : term}
   | THM of {arguments : arguments, goal : jdg, script : term}
   | TAC of {arguments : arguments, script : term}
   | PRINT_EXTRACT of Pos.t option * value
   | EXTRACT of value
   | NU of metas * cmd
   | TERM_ABS of metas * term
   | THM_ABS of string option * metas * jdg * term

   | BIND of cmd * id * cmd
   | RET of value
   | FORCE of value
   | FN of id * vty * cmd
   | AP of cmd * value
   | PRINT of Pos.t option * value
   | REFINE of string option * jdg * term
   | FRESH of (string option * Tm.valence) list
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
  type metavariable = Tm.metavariable
  type jdg = AtomicJudgment.jdg
  type term = Tm.abt
  type vty = MlType.vty

  type metas = (metavariable * Tm.valence) list

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
   | FRESH of (string option * Tm.valence) list
   | MATCH_METAS of value * metavariable list * cmd
   | MATCH_ABS of value * id * id * cmd
   | MATCH_THM of value * id * id * cmd
   | ABORT
end