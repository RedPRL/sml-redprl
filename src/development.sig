(* A development is an equational signature. *)
signature DEVELOPMENT =
sig
  type opid = string

  structure Abt : ABT
  structure Telescope : TELESCOPE
    where type label = opid

  type symctx = (Abt.symbol * Abt.sort) list

  (* the abstract type of valid declarations *)
  type decl
  type development = decl Telescope.telescope

  (* A declaration [Op[Y](Theta) := M] is valid in case
   * [M] is a closed term that takes symbols in [Y] and metavariables
   * in [Theta].
   *
   * The data of a declaration can be used to generate a family of operators,
   * taking its index in [Y], and deriving its arity from [Theta]
   * and [M]. *)
  datatype view = DECL of symctx * Abt.metacontext * Abt.abt

  (* throws [InvalidDecl] *)
  val decl : view -> decl
  exception InvalidDecl

  val view : decl -> view
end
