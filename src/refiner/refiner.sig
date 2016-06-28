signature REFINER =
sig
  structure Lcf : DEPENDENT_LCF

  type symbol = RedPrlAbt.symbol
  type metavariable = RedPrlAbt.metavariable
  type abt = RedPrlAbt.abt

  type 'a choice_sequence = int -> 'a

  (* a [name_store] is a choice sequence of names, i.e. a total function from
   * natural numbers to symbols. *)
  type name_store = symbol choice_sequence

  type ntactic = name_store -> Lcf.tactic
  type nmultitactic = name_store -> Lcf.multitactic

  val Elim
    : symbol      (* target *)
    -> ntactic

  val Eta
    : symbol
    -> ntactic

  val Intro
    : ntactic

  val Eq
    : int option (* rule index *)
    -> ntactic

  val CheckInfer
    : ntactic

  val Ext
    : ntactic

  val Cum
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
