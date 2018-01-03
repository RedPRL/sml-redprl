signature ML_SYNTAX =
sig
  type id
  type metavariable
  type jdg
  type term

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

  (* TODO: pretty printer *)
end
