structure Dim =
struct
  datatype 'i t =
     NAME of 'i
   | DIM0
   | DIM1

  val support =
    fn NAME u => [(u, SortData.DIM)]
     | _ => []

  fun eq f =
    fn (NAME u, NAME v) => f (u, v)
     | (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn NAME u => "dim[" ^ f u ^ "]"
     | DIM0 => "dim0"
     | DIM1 => "dim1"

  fun map f =
    fn NAME u => NAME (f u)
     | DIM0 => DIM0
     | DIM1 => DIM1

  local
    structure J = Json
  in
    fun encode f =
      fn NAME u => J.Obj [("dim", f u)]
       | DIM0 => J.String "dim0"
       | DIM1 => J.String "dim1"

    fun decode f =
      fn J.Obj [("dim", u)] => Option.map NAME (f u)
       | J.String "dim0" => SOME DIM0
       | J.String "dim1" => SOME DIM1
       | _ => NONE
  end
end

structure DimSpan =
struct
  type 'i t =
    {starting : 'i Dim.t,
     ending : 'i Dim.t}

  fun new (r, r') =
    {starting = r,
     ending = r'}

  fun support {starting, ending} =
    Dim.support starting @ Dim.support ending

  fun eq f (s1 : 'i t, s2 : 'i t) =
    Dim.eq f (#starting s1, #starting s2)
      andalso Dim.eq f (#ending s1, #ending s2)

  fun toString f {starting, ending} =
    Dim.toString f starting
      ^ " ~> "
      ^ Dim.toString f ending

  fun map f {starting, ending} =
    {starting = Dim.map f starting,
     ending = Dim.map f ending}

  local
    structure J = Json
  in
    fun encode f {starting, ending} =
      J.Obj
        [("starting", Dim.encode f starting),
         ("ending", Dim.encode f ending)]

    fun decode f =
      fn J.Obj [("starting", starting), ("ending", ending)] =>
         (case (Dim.decode f starting, Dim.decode f ending) of
             (SOME r, SOME r') => SOME {starting = r, ending = r'}
           | _ => NONE)
       | _ => NONE
  end
end

structure CubicalOperators =
struct
  structure Sort = RedPrlAtomicSort

  (* values *)
  datatype 'i cub_value =
     TUBE_SLICE_LIT of 'i Dim.t (* TODO: remove *)

  (* computations/continuations *)
  datatype 'i cub_cont =
     COE of 'i DimSpan.t
   | HCOM of 'i Dim.t list * 'i DimSpan.t (* homogeneous kan composition *)
end

structure CubicalV : JSON_ABT_OPERATOR =
struct
  open CubicalOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i cub_value
  infix <> ->>

  val arity =
    fn TUBE_SLICE_LIT extent =>
         [[DIM] * [] <> EXP, (* the 0 face *)
          [DIM] * [] <> EXP] (* the 1 face *)
             ->> TUBE_SLICE

  val support =
    fn TUBE_SLICE_LIT extent => Dim.support extent

  fun eq f =
    fn (TUBE_SLICE_LIT extent1, TUBE_SLICE_LIT extent2) => Dim.eq f (extent1, extent2)

  fun toString f =
    fn TUBE_SLICE_LIT extent => "tube[" ^ Dim.toString f extent ^ "]"

  fun map f =
    fn TUBE_SLICE_LIT extent => TUBE_SLICE_LIT (Dim.map f extent)

  local
    structure J = Json and S = RedPrlAtomicSortJson
  in
    fun encode f =
      fn TUBE_SLICE_LIT extent => J.Obj [("tube", Dim.encode f extent)]

    fun decode f =
      fn J.Obj [("tube", extent)] => Option.map TUBE_SLICE_LIT (Dim.decode f extent)
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
    fn COE _ => [[] * [] <> EXP] ->> EXP
     | HCOM (extents, span) =>
         let
           val cap = [] * [] <> EXP
           val tube = List.tabulate (Int.* (2, List.length extents), fn _ => [DIM] * [] <> EXP)
         in
           cap :: tube ->> EXP
         end


  val support =
    fn COE span => DimSpan.support span
     | HCOM (extents, span) => List.foldl (fn (r, xs) => Dim.support r @ xs) (DimSpan.support span) extents

  fun eq f =
    fn (COE s1, COE s2) => DimSpan.eq f (s1, s2)
     | (HCOM (es1, s1), HCOM (es2, s2)) => ListPair.allEq (Dim.eq f) (es1, es2) andalso DimSpan.eq f (s1, s2)
     | _ => false

  fun map f =
    fn COE s => COE (DimSpan.map f s)
     | HCOM (es, s) => HCOM (List.map (Dim.map f) es, DimSpan.map f s)

  fun toString f =
    fn COE s => "coe[" ^ DimSpan.toString f s ^ "]"
     | HCOM (es, s) =>
         "hcom["
           ^ ListSpine.pretty (Dim.toString f) "," es
           ^ "]{"
           ^ DimSpan.toString f s
           ^ "}"

  local
    structure J = Json

    (* TODO: remove copy-pasta and make OptionUtil public *)
    fun traverseOpt f xs =
      SOME (List.map (Option.valOf o f) xs)
        handle _ => NONE

    fun ** (SOME a, SOME b) = SOME (a, b)
      | ** _ = NONE

    infix **
  in
    fun encode f =
      fn COE s => J.Obj [("coe", DimSpan.encode f s)]
       | HCOM (es, s) => J.Obj [("hcom", J.Obj [("extents", J.Array (List.map (Dim.encode f) es)), ("span", DimSpan.encode f s)])]

    fun decode f =
      fn J.Obj [("coe", s)] => Option.map COE (DimSpan.decode f s)
       | J.Obj [("hcom", J.Obj [("extents", J.Array es), ("span", s)])] => Option.map HCOM (traverseOpt (Dim.decode f) es ** DimSpan.decode f s)
       | _ => NONE
  end

  val input =
    fn COE _ => ([DIM], EXP)
     | HCOM _ => ([], EXP)
end
