signature METALANGUAGE_MONAD = 
sig
  type names = int -> RedPrlAbt.symbol

  type 'a m
  val pure : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val map : ('a -> 'b) -> 'a m -> 'b m
  val get : Lcf.jdg m 
  val rule : (names -> Lcf.jdg Lcf.tactic) -> unit m
  val fork : unit m list -> unit m
  val orelse_ : 'a m * 'a m -> 'a m
end