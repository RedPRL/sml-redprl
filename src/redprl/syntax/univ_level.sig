signature REDPRL_LEVEL =
sig
  type level
  type t = level

  type term

  val const : IntInf.int -> level (* the input must >= 0 *)
  val zero : level
  val plus : level * IntInf.int -> level (* the second argument must >= 0 *)
  val succ : level -> level
  val join : level * level -> level
  val max : level list -> level

  val <= : level * level -> bool
  val < : level * level -> bool
  val eq : level * level -> bool

  val residual : level * level -> level option

  val into : level -> term
  val out : term -> level
  val map : (term -> term) -> level -> level
end
