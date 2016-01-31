signature SMALL_STEP =
sig
  datatype 'a t =
      STEP of 'a
    | FINAL

  val map : ('a -> 'b) -> 'a t -> 'b t
  val ret : 'a -> 'a t
  val bind : ('a -> 'b t) -> 'a t -> 'b t
end
