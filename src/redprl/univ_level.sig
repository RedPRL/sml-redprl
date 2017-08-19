signature REDPRL_LEVEL =
sig
  type level
  type t = level
  type param

  val const : IntInf.int -> level
  val zero : level
  val above : level * IntInf.int -> level
  val max : level list -> level

  val <= : level * level -> bool
  val eq : level * level -> bool
  val isZero : level -> bool

  val pretty : level -> Fpp.doc

  val into : level -> param
  val out : param -> level
end
