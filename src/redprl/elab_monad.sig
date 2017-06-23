signature ELAB_MONAD =
sig
  include MONAD_UTIL

  type 'a ann = Pos.t option * 'a

  val delay : (unit -> 'a t) -> 'a t
  val wrap : (unit -> 'a) ann -> 'a t

  val hush : 'a t -> 'a t
  val warn : Fpp.doc ann -> unit t
  val dump : Fpp.doc ann -> unit t
  val info : Fpp.doc ann -> unit t
  val fail : Fpp.doc ann -> 'a t

  type ('a, 'b) alg =
    {warn : Fpp.doc ann * 'b -> 'b,
     dump : Fpp.doc ann * 'b -> 'b,
     info : Fpp.doc ann * 'b -> 'b,
     init : 'b,
     fail : Fpp.doc ann * 'b -> 'b,
     succeed : 'a * 'b -> 'b}

  val fold : ('a, 'b) alg -> 'a t -> 'b
end

signature ELAB_MONAD_UTIL =
sig
  include ELAB_MONAD

  val run : 'a t -> 'a option
end
