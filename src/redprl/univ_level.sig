signature REDPRL_LEVEL =
sig
  type level
  type t = level

  val <= : level * level -> bool

  val const : IntInf.int -> level
  val zero : level
  val above : level * IntInf.int -> level
  val max : level list -> level

  val fromParam : Sym.t RedPrlParameterTerm.term -> level
  val toParam : level -> Sym.t RedPrlParameterTerm.term
end
