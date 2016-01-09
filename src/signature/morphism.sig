signature SIGNATURE_MORPHISM =
sig
  structure S1 : SIGNATURE
  structure S2 : SIGNATURE

  type metacontext
  val metacontext : S2.sign -> S2.arguments -> metacontext

  val symbol : S1.symbol -> S2.symbol
  val metavariable : S1.metavariable -> S2.metavariable

  val sort : S2.sign -> S1.sort -> S2.sort
  val valence : S2.sign -> S1.valence -> S2.valence

  val term : S2.sign -> metacontext * S2.symbols * S2.sort -> S1.term -> S2.term
  val notation : S1.notation -> S2.notation
end

