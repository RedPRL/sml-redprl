structure CubicalOperators =
struct
  structure Sort = RedPrlAtomicSort

  (* values *)
  datatype 'i cub_value =
     DIMREF of 'i (* dimension references *)
   | DIM0
   | DIM1

  (* computations/continuations *)
  datatype 'i cub_cont =
     COE
   | HCOM of int (* homogeneous kan composition *)

  (* definitional extensions *)
  datatype 'i cub_def =
     COM of int (* heterogeneous kan composition *)
end

structure CubicalV : JSON_ABT_OPERATOR =
struct
  open CubicalOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i cub_value
  infix <> ->>

  val arity =
    fn DIMREF a => [] ->> DIM
     | DIM0 => [] ->> DIM
     | DIM1 => [] ->> DIM

  val support =
    fn DIMREF a => [(a, DIM)]
     | DIM0 => []
     | DIM1 => []

  fun eq f =
    fn (DIMREF a, DIMREF b) => f (a, b)
     | (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn DIMREF a => "dim[" ^ f a ^ "]"
     | DIM0 => "dim0"
     | DIM1 => "dim1"

  fun map f =
    fn DIMREF a => DIMREF (f a)
     | DIM0 => DIM0
     | DIM1 => DIM1

  local
    structure J = Json
    structure S = RedPrlAtomicSortJson
  in
    fun encode f =
      fn DIMREF a => J.Obj [("dim", f a)]
       | DIM0 => J.String "dim0"
       | DIM1 => J.String "dim1"

    fun decode f =
      fn J.Obj [("dim", a)] => Option.map DIMREF (f a)
       | J.String "dim0" => SOME DIM0
       | J.String "dim1" => SOME DIM1
       | _ => NONE
  end
end

structure CubicalK :
sig
  include JSON_ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicSort.t
end =
struct
  open CubicalOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i cub_cont
  infix <> ->>

  (*datatype cub_cont =
     COE
   | HCOM of int (* homogeneous kan composition *)*)

  val arity =
    fn COE =>
         [[] * [] <> DIM,
          [] * [] <> DIM,
          [] * [] <> EXP]
            ->> EXP


  fun support _ = raise Match
  fun eq _ = raise Match
  fun map _ = raise Match
  fun toString _ = raise Match
  fun encode _ = raise Match
  fun decode _ = raise Match
  fun input _ = raise Match
end

(*

structure CubicalD : JSON_ABT_OPERATOR =
struct
end*)
structure CubicalD = struct end
