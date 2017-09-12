signature REFINER =
sig
  type sign
  type abt
  type catjdg
  type rule
  type hyp
  type opid
  type param
  type psort
  type 'a bview

  val Cut : catjdg -> rule
  val CutLemma : sign -> opid -> (param * psort option) list -> rule

  val Elim : sign -> hyp -> rule
  val Rewrite : sign -> hyp -> rule
  val Internalize : sign -> rule
  val AutoStep : sign -> rule

  structure Equality :
  sig
    val Symmetry : rule
  end

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

  val SynthFromHyp : hyp -> rule

  val Exact : abt -> rule


  type rule_name = string
  val lookupRule : rule_name -> rule
end
