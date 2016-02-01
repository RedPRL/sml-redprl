signature REFINER =
sig
  structure Tacticals : TACTICALS

  type abt
  type symbol

  type 'a choice_sequence = int -> 'a

  (* a [name_store] is a choice sequence of names, i.e. a total function from
   * natural numbers to symbols. *)
  type name_store = symbol choice_sequence

  type ntactic = name_store -> Tacticals.Lcf.tactic

  val Rec
    : (ntactic -> ntactic)
    -> ntactic

  val Elim
    : symbol       (* target *)
    -> abt option (* optional argument *)
    -> ntactic

  val Intro
    : int option   (* rule index *)
    -> abt option (* optional argument *)
    -> ntactic

  val Hyp
    : symbol (* target *)
    -> ntactic
end

signature ELABORATOR =
sig
  structure Signature : ABT_SIGNATURE

  type symbol = Signature.Abt.symbol
  type abt = Signature.Abt.abt

  structure Refiner : REFINER
    where type symbol = symbol
    where type abt = abt

  type env = Refiner.ntactic Signature.Abt.VarCtx.dict

  val elaborate : Signature.sign -> env -> abt -> Refiner.ntactic
  val elaborate' : Signature.sign -> abt -> Refiner.ntactic
end
