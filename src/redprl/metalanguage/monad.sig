signature METALANGUAGE_MONAD = 
sig
  type name = RedPrlAbt.symbol
  type names = int -> name

  type 'a m
  val pure : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val multibind : unit m -> unit m list -> unit m
  
  val map : ('a -> 'b) -> 'a m -> 'b m
  val getGoal : Lcf.jdg m 
  val rule : (names -> Lcf.jdg Lcf.tactic) -> unit m
  val orelse_ : 'a m * 'a m -> 'a m

  val extract : Pos.t option -> 'a m -> Lcf.L.term m

  val local_ : Lcf.jdg -> unit m -> unit m
  val pushNames : name list * 'a m -> 'a m

  val print : Pos.t option * Fpp.doc -> unit m
  val fail : Pos.t option * Fpp.doc -> 'a m

  val run : 'a m -> unit
end

signature MONAD_ALTERNATIVE = 
sig
  include MONAD
  val fail : 'a m
  val <+> : 'a m * 'a m -> 'a m
end

(* Another idea, where we distinguish between local and global tactics. *)
signature METALANGUAGE_MONAD2 = 
sig
  type name = RedPrlAbt.variable
  type names = int -> name

  structure L : MONAD_ALTERNATIVE (* LOCAL *)
  structure G : MONAD_ALTERNATIVE (* GLOBAL *)

  val enter : 'a L.m -> 'a list G.m
  val fork : 'a L.m list -> 'a list G.m
  val unfocus : 'a G.m -> 'a L.m

  val goal : Lcf.jdg L.m
  val rule : (names -> Lcf.jdg Lcf.tactic) -> unit L.m
end