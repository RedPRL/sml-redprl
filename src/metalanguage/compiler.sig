signature REFINER =
sig
  type tactic
  structure Tacticals : TACTICALS where type tactic = tactic

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

signature COMPILER =
sig
  structure Refiner : REFINER

  val compile : Abt.abt -> Refiner.tactic
end
