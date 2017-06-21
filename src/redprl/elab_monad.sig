signature ELAB_MONAD =
sig
  include MONAD_UTIL

  type 'a ann = Pos.t option * 'a

  val delay : (unit -> 'a t) -> 'a t
  val wrap : (unit -> 'a) ann -> 'a t

  val hush : 'a t -> 'a t
  val warn : FinalPrinter.doc ann -> unit t
  val dump : FinalPrinter.doc ann -> unit t
  val info : FinalPrinter.doc ann -> unit t
  val fail : FinalPrinter.doc ann -> 'a t

  type ('a, 'b) alg =
    {warn : FinalPrinter.doc ann * 'b -> 'b,
     dump : FinalPrinter.doc ann * 'b -> 'b,
     info : FinalPrinter.doc ann * 'b -> 'b,
     init : 'b,
     fail : FinalPrinter.doc ann * 'b -> 'b,
     succeed : 'a * 'b -> 'b}

  val fold : ('a, 'b) alg -> 'a t -> 'b
end

signature ELAB_MONAD_UTIL =
sig
  include ELAB_MONAD

  val run : 'a t -> 'a option
end
