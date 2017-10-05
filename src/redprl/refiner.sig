signature REFINER =
sig
  type sign
  type abt
  type catjdg
  type rule
  type hyp
  type opid
  type 'a bview

  val Cut : catjdg -> rule
  val CutLemma : sign -> opid -> rule

  val AutoStep : sign -> rule
  val Elim : sign -> hyp -> rule
  val Exact : abt -> rule
  val Rewrite : sign -> hyp RedPrlOpData.selector -> abt -> rule
  val RewriteHyp : sign -> hyp RedPrlOpData.selector -> hyp -> rule
  val Symmetry : rule
  val SynthFromHyp : hyp -> rule

  structure Custom :
  sig
    val UnfoldAll : sign -> opid list -> rule
    val Unfold : sign -> opid list -> hyp RedPrlOpData.selector list -> rule
  end

  structure Computation :
  sig
    val ReduceAll : sign -> rule
    val Reduce : sign -> hyp RedPrlOpData.selector list -> rule
  end

  structure Hyp :
  sig
    val Project : hyp -> rule
    val Rename : hyp -> rule
    val Delete : hyp -> rule
  end

  structure Tactical :
  sig
    val NormalizeGoalDelegate : (abt -> rule) -> sign -> rule
    val NormalizeHypDelegate : (abt -> hyp -> rule) -> sign -> hyp -> rule
  end

  type rule_name = string
  val lookupRule : rule_name -> rule
end
