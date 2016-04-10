signature REFINER =
sig
  structure Tacticals : TACTICALS
    where type Lcf.J.Tm.abt = Abt.abt
    where type Lcf.J.Tm.Metavariable.t = Abt.metavariable

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

  val Eq
    : int option (* rule index *)
    -> ntactic

  val Ext
    : ntactic

  val Hyp
    : symbol (* target *)
    -> ntactic

  val Unhide
    : symbol (* target *)
    -> ntactic

  val CStep
    : AbtSignature.sign
    -> int
    -> ntactic

  val CSym
    : ntactic

  val CEval
    : AbtSignature.sign
    -> ntactic

  val RewriteGoal
    : abt
    -> ntactic

  val EvalGoal
    : AbtSignature.sign
    -> Target.target
    -> ntactic

  val Witness
    : abt
    -> ntactic

  val AutoStep
    : AbtSignature.sign
    -> ntactic

  val Unfold
    : AbtSignature.sign
    -> symbol
    -> Target.target
    -> ntactic

  val Normalize
    : AbtSignature.sign
    -> Target.target
    -> ntactic

end


