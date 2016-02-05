signature REFINER =
sig
  structure Abt : ABT
  structure Telescope : TELESCOPE
  structure Tacticals : TACTICALS
  sharing type Tacticals.Lcf.ctx = Telescope.telescope
  sharing type Tacticals.Lcf.evidence = Abt.abs
  sharing type Telescope.Label.t = Abt.Metavariable.t

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
    -> abt option (* optional argument *)
    -> ntactic

  val Intro
    : int option  (* rule index *)
    -> abt option (* optional argument *)
    -> ntactic

  val Hyp
    : symbol (* target *)
    -> ntactic
end


