signature REFINER =
sig
  structure Telescope : TELESCOPE
    where type Label.t = Abt.metavariable
  structure Tacticals : TACTICALS
    where type Lcf.evidence = Abt.abs
    where type 'a Lcf.ctx = 'a Telescope.telescope

  type symbol = Abt.symbol
  type metavariable = Abt.metavariable
  type abt = Abt.abt

  type 'a choice_sequence = int -> 'a

  (* a [name_store] is a choice sequence of names, i.e. a total function from
   * natural numbers to symbols. *)
  type name_store = symbol choice_sequence

  type ntactic = name_store -> Tacticals.Lcf.tactic

  val Elim
    : symbol      (* target *)
    -> ntactic

  val Intro
    : int option  (* rule index *)
    -> ntactic

  val Hyp
    : symbol (* target *)
    -> ntactic

  val CStep
    : AbtSignature.sign
    -> int
    -> ntactic

  val CSym : ntactic
  val CEval : AbtSignature.sign -> ntactic
end


