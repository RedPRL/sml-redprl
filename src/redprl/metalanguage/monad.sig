signature METALANGUAGE_MONAD = 
sig
  type name = RedPrlAbt.symbol
  type names = int -> name

  type 'a m
  val pure : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val map : ('a -> 'b) -> 'a m -> 'b m
  val getGoal : Lcf.jdg m 
  val rule : (names -> Lcf.jdg Lcf.tactic) -> unit m
  val fork : unit m list -> unit m
  val orelse_ : 'a m * 'a m -> 'a m

  val extract : 'a m -> Lcf.L.term m

  val set : Lcf.jdg -> unit m
  val local_ : Lcf.jdg -> unit m -> unit m
  val pushNames : name list * 'a m -> 'a m

  val print : Pos.t option * Fpp.doc -> unit m
  val fail : Pos.t option * Fpp.doc -> 'a m
end