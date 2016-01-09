signature SIGNATURE_MORPHISM =
sig
  structure S1 : SIGNATURE
  structure S2 : SIGNATURE

  val symbol : S1.symbol -> S2.symbol

  val sort : S2.sign -> S1.sort -> S2.sort
  val arguments  : S2.sign -> S1.arguments -> S2.arguments
  val term : S2.sign -> S1.term -> S2.term
  val notation : S1.notation -> S2.notation
end

