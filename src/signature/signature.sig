signature SIGNATURE =
sig
  type opid = string

  structure Abt : ABT
  structure Telescope : TELESCOPE
    where type label = opid

  type symctx = (Abt.symbol * Abt.sort) list

  (* abstract types for declarations *)
  type def
  type notation

  type decl =
    {def : def,
     notation : notation option}

  (* A signature / [sign] is a telescope of declarations. *)
  type sign = decl Telescope.telescope

  (* A definition [Op[Y](Theta) := M] is valid in case
   * [M] is a closed term that takes symbols in [Y] and metavariables
   * in [Theta].
   *
   * The data of a definition can be used to generate a family of operators,
   * taking its index in [Y], and deriving its arity from [Theta]
   * and [M]. *)
  datatype def_view = DEF of symctx * Abt.metacontext * Abt.abt

  (* throws [InvalidDef] *)
  val def : def_view -> def
  exception InvalidDef

  val view : def -> def_view
end
