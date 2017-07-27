signature REFINER =
sig
  type sign
  type abt
  type catjdg
  type rule
  type hyp
  type opid
  type param
  type 'a bview

  val Lemma : sign -> opid -> param list -> rule
  val Cut : catjdg -> rule
  val CutLemma : sign -> opid -> param list -> rule

  val Elim : sign -> hyp -> rule
  val AutoStep : sign -> rule

  structure Equality :
  sig
    val Symmetry : rule
  end

  structure Computation :
  sig
    val Unfold : sign -> opid -> rule
    val EqHeadExpansion : sign -> rule
  end

  structure Hyp :
  sig
    val Project : hyp -> rule
    val Rename : hyp -> rule
    val Delete : hyp -> rule
  end

  structure Synth :
  sig
    val FromWfHyp : hyp -> rule
  end

  val Exact : abt -> rule


  type rule_name = string
  val lookupRule : rule_name -> rule
end
