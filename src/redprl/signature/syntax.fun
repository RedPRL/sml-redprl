functor MlSyntax
  (type id
   type metavariable
   type jdg
   type term) : ML_SYNTAX = 
struct
  type id = id
  type metavariable = metavariable
  type jdg = jdg
  type term = term

  type bindings = (metavariable * Tm.valence) list

  datatype value =
     THUNK of cmd
   | VAR of id
   | NIL
   | ABS of value * value
   | METAS of bindings
   | TERM of term

  and cmd =
     BIND of cmd * id * cmd
   | RET of value
   | FORCE of value
   | PRINT of Pos.t option * value
   | REFINE of jdg * term
   | NU of bindings * cmd
   | MATCH_ABS of value * id * id * cmd
   | EXTRACT of value
   | ABORT
end
