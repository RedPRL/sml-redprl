signature ELAB_MONAD =
sig
  include MONAD_UTIL

  type 'a ann = Pos.t option * 'a

  val wrap : (unit -> 'a) ann -> 'a t

  val warn : string ann -> unit t
  val info : string ann -> unit t
  val fail : string ann -> 'a t

  type ('a, 'b) alg =
    {warn : string ann * 'b -> 'b,
     info : string ann * 'b -> 'b,
     init : 'b,
     fail : string ann * 'b -> 'b,
     succeed : 'a * 'b -> 'b}

  val fold : ('a, 'b) alg -> 'a t -> 'b
end

signature ELAB_MONAD_UTIL =
sig
  include ELAB_MONAD

  val run : 'a t -> 'a option
end
