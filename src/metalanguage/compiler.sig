signature REFINER =
sig
  type tactic
  structure Tacticals : TACTICALS where type tactic = tactic

  val Elim
    : Symbol.t  (* target *)
    -> Symbol.t list (* fresh names *)
    -> Abt.abt option (* optional argument *)
    -> tactic

  val Intro
    : int option (* rule index *)
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
