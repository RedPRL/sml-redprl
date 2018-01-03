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

  datatype value =
     THUNK of cmd
   | VAR of id
   | NIL
   | ABS of (metavariable * Tm.valence) list * value
   | TERM of term

  and cmd =
     BIND of cmd * id * cmd
   | RET of value
   | FORCE of value
   | PRINT of Pos.t option * value
   | REFINE of jdg * term
   | NU of (metavariable * Tm.valence) list * cmd
   | EXTRACT of value
   | ABORT
end
