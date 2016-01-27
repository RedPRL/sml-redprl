signature REFINER =
sig
  structure Lcf : LCF
  structure Tacticals : TACTICALS
    where type tactic = Lcf.tactic

  type 'a choice_sequence = int -> 'a

  (* a [name_store] is a choice sequence of names, i.e. a total function from
   * natural numbers to symbols. *)
  type name_store = Symbol.t choice_sequence

  type ntactic = name_store -> Lcf.tactic

  val Rec
    : (ntactic -> ntactic)
    -> ntactic

  val Elim
    : Symbol.t  (* target *)
    -> Abt.abt option (* optional argument *)
    -> ntactic

  val Intro
    : int option (* rule index *)
    -> Abt.abt option (* optional argument *)
    -> ntactic

  val Hyp
    : Symbol.t (* target *)
    -> ntactic
end

signature ELABORATOR =
sig
  structure Refiner : REFINER

  structure Env : DICT where type key = Variable.t
  type env = Refiner.ntactic Env.dict
  val elaborate : env -> Abt.abt -> Refiner.ntactic
end
