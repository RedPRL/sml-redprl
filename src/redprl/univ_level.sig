signature REDPRL_LEVEL =
sig
  type level
  type t = level

  type term

  val const : IntInf.int -> level
  val zero : level
  val above : level * IntInf.int -> level
  val max : level list -> level

  val <= : level * level -> bool
  val < : level * level -> bool
  val eq : level * level -> bool
  val residual : level * level -> level option

  val pretty : level -> Fpp.doc

  val into : level -> term
  val out : term -> level
end
