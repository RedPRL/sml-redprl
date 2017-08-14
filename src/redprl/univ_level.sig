signature REDPRL_LEVEL =
sig
  type level
  type t = level

  val <= : level * level -> bool
  val succ : level -> level

  val fromParam : Sym.t RedPrlParameterTerm.term -> level
  val toParam : level -> Sym.t RedPrlParameterTerm.term
end
