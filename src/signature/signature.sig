signature SIGNATURE =
sig
  type symbol
  type sort
  type metavariable
  type valence
  type term

  type symbols = (symbol * sort) list
  type arguments = (metavariable * valence) list

  (* abstract types for declarations *)
  type def
  type notation

  type decl =
    {def : def,
     notation : notation option}

  (* A signature / [sign] is a telescope of declarations. *)
  type sign = decl StringTelescope.telescope

  datatype def_view = DEF of symbols * arguments * sort * term

  (* throws [InvalidDef] *)
  val def : def_view -> def
  exception InvalidDef

  val view : def -> def_view
end
