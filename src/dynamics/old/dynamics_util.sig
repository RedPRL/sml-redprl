signature DYNAMICS_UTIL =
sig
  include DYNAMICS

  (* execute a suspended substitution *)
  val force : abt closure -> abt

  val stepn : sign -> int -> abt -> abt
  val step' : sign -> abt -> abt step

  val eval : sign -> (Signature.Abt.metaenv * Signature.Abt.symenv * Signature.Abt.varenv) -> abt -> abt
  val evalClosed : sign -> abt -> abt
  val evalOpen : sign -> abt -> abt
end

