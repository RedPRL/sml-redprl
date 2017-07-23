signature CATEGORICAL_JUDGMENT =
sig
  type ('sym, 'a) jdg

  val map : ('sym1 -> 'sym2) -> ('a -> 'b) -> ('sym1, 'a) jdg -> ('sym2, 'b) jdg
  val map_ : ('a -> 'b) -> ('sym, 'a) jdg -> ('sym, 'b) jdg

  structure Tm : ABT
  type abt = Tm.abt
  type sort = Tm.sort

  (* What sort of term does the jdg synthesize? *)
  val synthesis : ('sym, 'a) jdg -> sort

  val toAbt : (Sym.t, abt) jdg -> abt
  val fromAbt : abt -> (Sym.t, abt) jdg

  val metactx : (Sym.t, abt) jdg -> Tm.metactx

  val eq : (Sym.t, abt) jdg * (Sym.t, abt) jdg -> bool

  val pretty : ('a * 'a -> bool) -> ('a -> Fpp.doc) -> (Sym.t, 'a) jdg -> Fpp.doc
  val pretty' : ('a -> Fpp.doc) -> (Sym.t, 'a) jdg -> Fpp.doc
end
