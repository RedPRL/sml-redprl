structure AtomOperators =
struct
  structure Sort = RedPrlAtomicSort

  datatype 'i atom_value =
      ATOM of Sort.t
    | TOKEN of 'i * Sort.t

  datatype 'i atom_cont =
      TEST0 of Sort.t * Sort.t
    | TEST1 of ('i * Sort.t) * Sort.t
end

structure AtomV : JSON_ABT_OPERATOR =
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

  local
    structure J = Json
    structure S = RedPrlAtomicSortJson
  in
    fun encode f =
      fn ATOM tau => J.Obj [("atom", S.encode tau)]
       | TOKEN (u, tau) => J.Obj [("token", f u), ("sort", S.encode tau)]

    fun decode f =
      fn J.Obj [("atom", tau)] => Option.map ATOM (S.decode tau)
       | J.Obj [("token", u), ("sort", tau)] =>
           (case (f u, raise Match) of
               (SOME u', SOME tau') => SOME (TOKEN (u', tau'))
             | _ => NONE)
       | _ => NONE
  end
end

structure AtomK :
sig
  include JSON_ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicSort.t
end =
struct
  open AtomOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i atom_cont
  infix <> ->>

  val arity =
    fn TEST0 (_, tau) =>
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
    fn TEST0 (sigma, tau) => TEST0 (sigma, tau)
     | TEST1 ((u, sigma), tau) => TEST1 ((f u, sigma), tau)

  fun eq f =
    fn (TEST0 tau, TEST0 tau') => tau = tau'
     | (TEST1 ((u, sigma), tau), TEST1 ((v, sigma'), tau')) => f (u, v) andalso sigma = sigma' andalso tau = tau'
     | _ => false

  fun toString f =
    fn TEST0 (sigma, tau) => "ifeq0{" ^ Sort.toString tau ^ "}"
     | TEST1 ((u, _), tau) => "ifeq1{" ^ Sort.toString tau ^ "}[" ^ f u ^ "]"

  local
    structure J = Json and S = RedPrlAtomicSortJson
  in
    fun encode f =
      fn TEST0 (sigma, tau) => J.Obj [("test0", J.Obj [("sorts", J.Array [S.encode sigma, S.encode tau])])]
       | TEST1 ((u, sigma), tau) => J.Obj [("test1", J.Obj [("sym", f u), ("sorts", J.Array [S.encode sigma, S.encode tau])])]

    fun decode f =
      fn J.Obj [("test0", J.Obj [("sorts", J.Array [sigma, tau])])] =>
           (case (S.decode sigma, S.decode tau) of
               (SOME sigma', SOME tau') => SOME (TEST0 (sigma', tau'))
             | _ => NONE)
       | J.Obj [("test1", J.Obj [("sym", u), ("sorts", J.Array [sigma, tau])])] =>
           (case (f u, S.decode sigma, S.decode tau) of
               (SOME u', SOME sigma', SOME tau') => SOME (TEST1 ((u', sigma'), tau'))
             | _ => NONE)
       | _ => NONE
  end
end
