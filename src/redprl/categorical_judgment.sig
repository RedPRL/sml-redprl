signature CATEGORICAL_JUDGMENT =
sig
  type 'a jdg

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg

  structure Tm : ABT
  type abt = Tm.abt
  type sort = Tm.sort

  (* What sort of term does the jdg synthesize? *)
  val synthesis : 'a jdg -> sort

  val toAbt : abt jdg -> abt
  val fromAbt : abt -> abt jdg

  val metactx : abt jdg -> Tm.metactx
  val unify : abt jdg * abt jdg -> Tm.Unify.renaming

  val eq : abt jdg * abt jdg -> bool

  val pretty : ('a * 'a -> bool) -> ('a -> Fpp.doc) -> 'a jdg -> Fpp.doc
  val pretty' : ('a -> Fpp.doc) -> 'a jdg -> Fpp.doc

  exception InvalidJudgment
end
