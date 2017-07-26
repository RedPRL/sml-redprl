signature SPREAD =
sig
  (* A choice sequence, or an "ideal point". *)
  type 'a point

  (* A finite approximation, or a "neighborhood". *)
  type 'a neigh = 'a list

  val map
    : ('a -> 'b)
    -> 'a point
    -> 'b point

  (* Take the [i]th element in the choice sequence. *)
  val at
    : 'a point
    -> int
    -> 'a

  (* Prepend elements to the front of the choice sequence. *)
  val prepend
    : 'a neigh
    -> 'a point
    -> 'a point

  (* Remove [n] elements from the front of the choice sequence. *)
  val bite
    : int
    -> 'a point
    -> 'a point

  (* Booby-trap a choice sequence to witness continuity theorems; by
   * passing a "probed" choice sequence to a functional, you can calculate
   * the functional's modulus of continuity by observing the returned
   * reference. *)
  val probe
    : 'a point
    -> 'a point * int ref

end
