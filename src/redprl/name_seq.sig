signature NAME_SEQ =
sig
  type 'a seq

  (* Take the [i]th element in the sequence. *)
  val at
    : 'a seq
    -> int
    -> 'a

  (* Prepend elements to the front of the choice sequence. *)
  val prepend
    : 'a list
    -> 'a seq
    -> 'a seq

  (* Remove [n] elements from the front of the choice sequence. *)
  val bite
    : int
    -> 'a seq
    -> 'a seq

  (* Booby-trap a choice sequence to witness continuity theorems; by
   * passing a "probed" choice sequence to a functional, you can calculate
   * the functional's modulus of continuity by observing the returned
   * reference. *)
  val probe
    : 'a seq
    -> 'a seq * int ref
end
