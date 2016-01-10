signature REFINER =
sig
  type tactic
  structure Tacticals : TACTICALS where type tactic = tactic

  (* a [name_store] is a partial function from natural numbers to names;
   * built-in rules will query from the name store when they need a fresh name.
   *)
  type name_store = int -> Symbol.t

  val Elim
    : Symbol.t  (* target *)
    -> name_store (* fresh names *)
    -> Abt.abt option (* optional argument *)
    -> tactic

  val Intro
    : int option (* rule index *)
    -> name_store (* fresh names *)
    -> Abt.abt option (* optional argument *)
    -> tactic

  val Hyp
    : Symbol.t (* target *)
    -> tactic
end

signature ELABORATOR =
sig
  structure Refiner : REFINER

  val elaborate : Abt.abt -> Refiner.tactic
end
