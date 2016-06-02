structure AtomOperators =
struct
  structure Sort = RedPrlAtomicSort

  datatype 'i atom_value =
      ATOM of Sort.t
    | TOKEN of 'i * Sort.t

  datatype 'i atom_cont =
      TEST0 of Sort.t
    | TEST1 of ('i * Sort.t) * Sort.t
end


structure AtomV : ABT_OPERATOR =
struct
  open AtomOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i atom_value
  infix <> ->>

  val arity =
    fn ATOM _ => [] ->> EXP
     | TOKEN _ => [] ->> EXP

  val support =
    fn ATOM _ => []
     | TOKEN (u, tau) => [(u, tau)]

  fun eq f =
    fn (ATOM sigma, ATOM tau) => sigma = tau
     | (TOKEN (u, sigma), TOKEN (v, tau)) => f (u, v) andalso sigma = tau
     | _ => false

  fun toString f =
    fn ATOM tau => "atom{" ^ Sort.toString tau ^ "}"
     | TOKEN (u, tau) => "'" ^ f u ^ ":" ^ Sort.toString tau

  fun map f =
    fn ATOM tau => ATOM tau
     | TOKEN (u, tau) => TOKEN (f u, tau)
end

structure AtomK :
sig
  include ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicSort.t
end =
struct
  open AtomOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i atom_cont
  infix <> ->>

  val arity =
    fn TEST0 tau =>
         [[] * [] <> EXP,
          [] * [] <> tau,
          [] * [] <> tau]
            ->> tau
     | TEST1 (_, tau) =>
         [[] * [] <> tau,
          [] * [] <> tau]
            ->> tau

  val input =
    fn TEST0 _ => EXP
     | TEST1 _ => EXP

  val support =
    fn TEST0 _ => []
     | TEST1 ((u, sigma), _) => [(u, sigma)]

  fun map f =
    fn TEST0 tau => TEST0 tau
     | TEST1 ((u, sigma), tau) => TEST1 ((f u, sigma), tau)

  fun eq f =
    fn (TEST0 tau, TEST0 tau') => tau = tau'
     | (TEST1 ((u, sigma), tau), TEST1 ((v, sigma'), tau')) => f (u, v) andalso sigma = sigma' andalso tau = tau'
     | _ => false

  fun toString f =
    fn TEST0 tau => "ifeq0{" ^ Sort.toString tau ^ "}"
     | TEST1 ((u, _), tau) => "ifeq1{" ^ Sort.toString tau ^ "}[" ^ f u ^ "]"
end
