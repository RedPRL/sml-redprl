signature DYNAMICS_UTIL =
sig
  include DYNAMICS

  (* execute a suspended substitution *)
  val force : abt closure -> abt

  val step' : sign -> abt -> abt step

  val eval : sign -> (Signature.Abt.varenv * Signature.Abt.metaenv) -> abt -> abt
  val eval' : sign -> abt -> abt
end

