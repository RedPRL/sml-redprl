structure CubicalOperators =
struct
  structure Sort = RedPrlAtomicSort

  (* values *)
  datatype 'i cub_value =
     DIMREF of 'i (* dimension references *)
   | DIM0
   | DIM1
   | TUBE_SLICE_LIT (* an extent and two tube faces *)

  (* computations/continuations *)
  datatype 'i cub_cont =
     COE
   | HCOM (* homogeneous kan composition *)
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
     | TUBE_SLICE_LIT =>
         [[] * [] <> DIM, (* the extent *)
          [DIM] * [] <> EXP, (* the 0 face *)
          [DIM] * [] <> EXP] (* the 1 face *)
             ->> TUBE_SLICE

  val support =
    fn DIMREF a => [(a, DIM)]
     | DIM0 => []
     | DIM1 => []
     | TUBE_SLICE_LIT => []

  fun eq f =
    fn (DIMREF a, DIMREF b) => f (a, b)
     | (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | (TUBE_SLICE_LIT, TUBE_SLICE_LIT) => true
     | _ => false

  fun toString f =
    fn DIMREF a => "dim[" ^ f a ^ "]"
     | DIM0 => "dim0"
     | DIM1 => "dim1"
     | TUBE_SLICE_LIT => "tube-slice"

  fun map f =
    fn DIMREF a => DIMREF (f a)
     | DIM0 => DIM0
     | DIM1 => DIM1
     | TUBE_SLICE_LIT => TUBE_SLICE_LIT

  local
    structure J = Json
    structure S = RedPrlAtomicSortJson
  in
    fun encode f =
      fn DIMREF a => J.Obj [("dim", f a)]
       | DIM0 => J.String "dim0"
       | DIM1 => J.String "dim1"
       | TUBE_SLICE_LIT => J.String "tube-slice"

    fun decode f =
      fn J.Obj [("dim", a)] => Option.map DIMREF (f a)
       | J.String "dim0" => SOME DIM0
       | J.String "dim1" => SOME DIM1
       | J.String "tube-slice" => SOME TUBE_SLICE_LIT
       | _ => NONE
  end
end

structure CubicalK :
sig
  include JSON_ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicSort.t list * RedPrlAtomicSort.t
end =
struct
  open CubicalOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i cub_cont
  infix <> ->>

  val arity =
    fn COE =>
         [[] * [] <> DIM, (* starting dimension *)
          [] * [] <> DIM, (* ending dimension *)
          [] * [] <> EXP]
            ->> EXP
     | HCOM =>
         [[] * [] <> DIM, (* starting (cap) dimension *)
          [] * [] <> DIM, (* ending (composite) dimension *)
          [] * [] <> EXP, (* the cap *)
          [] * [] <> VEC TUBE_SLICE] (* the extents & their tube *)
            ->> EXP

  fun support _ = []

  fun eq f =
    fn (COE, COE) => true
     | (HCOM, HCOM) => true
     | _ => false

  fun map f =
    fn COE => COE
     | HCOM => HCOM

  fun toString f =
    fn COE => "coe"
     | HCOM => "hcom"

  local
    structure J = Json
  in
    fun encode f =
      fn COE => J.String "coe"
       | HCOM => J.String "hcom"

    fun decode f =
      fn J.String "coe" => SOME COE
       | J.String "hcom" => SOME HCOM
       | _ => NONE
  end

  val input =
    fn COE => ([DIM], EXP)
     | HCOM => ([], EXP)
end
