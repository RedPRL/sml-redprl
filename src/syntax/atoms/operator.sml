structure AtomOperators =
struct
  structure Sort = RedPRLAtomicSort

  datatype 'i atom_value =
      ATOM of Sort.t
    | TOKEN of 'i * Sort.t

  datatype atom_cont =
      TEST0 of Sort.t * Sort.t
    | TEST1 of Sort.t * Sort.t
end


structure AtomV : ABT_OPERATOR =
struct
  open AtomOperators SortData ArityNotation
  structure Ar = RedPRLAtomicArity

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

structure SimpleAtomK : ABT_SIMPLE_OPERATOR =
struct
  open AtomOperators SortData ArityNotation
  structure Ar = RedPRLAtomicArity

  type t = atom_cont
  infix <> ->>

  val arity =
    fn TEST0 (sigma, tau) =>
         [[] * [] <> EXP,
          [] * [] <> tau,
          [] * [] <> tau]
            ->> tau
     | TEST1 (sigma, tau) =>
         [[] * [] <> EXP,
          [] * [] <> tau,
          [] * [] <> tau]
            ->> tau

  val eq =
    fn (TEST0 (sigma, tau), TEST0 (sigma', tau')) =>
         sigma = sigma' andalso tau = tau'
     | (TEST1 (sigma, tau), TEST1 (sigma', tau')) =>
         sigma = sigma' andalso tau = tau'
     | _ => false

  val toString =
    fn TEST0 (sigma, tau) => "ifeq0{" ^ Sort.toString sigma ^ "," ^ Sort.toString tau ^ "}"
     | TEST1 (sigma, tau) => "ifeq0{" ^ Sort.toString sigma ^ "," ^ Sort.toString tau ^ "}"
end

structure AtomK = AbtSimpleOperator (SimpleAtomK)
