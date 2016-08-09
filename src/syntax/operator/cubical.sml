structure CubicalOperators =
struct
  structure Sort = RedPrlAtomicSort

  (* computations/continuations *)
  datatype 'i cub_cont =
     COE of 'i DimSpan.t
   | HCOM of 'i Dim.t list * 'i DimSpan.t (* homogeneous kan composition *)
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
