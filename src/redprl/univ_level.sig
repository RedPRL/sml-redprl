signature REDPRL_LEVEL =
sig
  type level
  type t = level

  val const : IntInf.int -> level
  val zero : level
  val above : level * IntInf.int -> level
  val max : level list -> level

  val <= : level * level -> bool
  val eq : level * level -> bool
  val isZero : level -> bool

  type sym
  val pretty' : (sym -> Fpp.doc) -> level -> Fpp.doc

  type param
  val into : level -> param
  val out : param -> level
end
