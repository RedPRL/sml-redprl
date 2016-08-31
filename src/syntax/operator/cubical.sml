structure CubicalOperators =
struct
  structure Sort = RedPrlAtomicSort

  datatype 'i cub_val =
     ID
   | ID_ABS
   | BOOL
   | BOOL_TT
   | BOOL_FF
   | BOOL_HCOM of 'i list * 'i DimSpan.t

  (* computations/continuations *)
  datatype 'i cub_cont =
     COE of 'i DimSpan.t
   | HCOM of 'i DimVec.t * 'i DimSpan.t (* homogeneous kan composition *)
   | ID_APP of 'i Dim.t
   | BOOL_IF
end

structure HcomUtil =
struct
  fun hcomArity extents =
     let
       open SortData ArityNotation
       infix <> ->>
       val cap = [] * [] <> EXP
       val tube = List.tabulate (Int.* (2, List.length extents), fn _ => [DIM] * [] <> EXP)
     in
       cap :: tube ->> EXP
     end
end

structure CubicalV : JSON_ABT_OPERATOR =
struct
  open CubicalOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i cub_val
  infix <> ->>

  val arity =
    fn ID =>
         [[DIM] * [] <> EXP,
          [] * [] <> EXP,
          [] * [] <> EXP]
            ->> EXP
     | ID_ABS => [[DIM] * [] <> EXP] ->> EXP
     | BOOL => [] ->> EXP
     | BOOL_TT => [] ->> EXP
     | BOOL_FF => [] ->> EXP
     | BOOL_HCOM (extents, _) => HcomUtil.hcomArity extents

  val support =
    fn BOOL_HCOM (extents, dir) => List.map (fn u => (u, DIM)) extents @ DimSpan.support dir
     | _ => []

  fun eq f =
    fn (ID, ID) => true
     | (ID_ABS, ID_ABS) => true
     | (BOOL, BOOL) => true
     | (BOOL_TT, BOOL_TT) => true
     | (BOOL_FF, BOOL_FF) => true
     | (BOOL_HCOM (es1, sp1), BOOL_HCOM (es2, sp2)) =>
         ListPair.allEq f (es1, es2)
           andalso DimSpan.eq f (sp1, sp2)
     | _ => false

  fun map f =
    fn ID => ID
     | ID_ABS => ID_ABS
     | BOOL => BOOL
     | BOOL_TT => BOOL_TT
     | BOOL_FF => BOOL_FF
     | BOOL_HCOM (extents, dir) => BOOL_HCOM (List.map f extents, DimSpan.map f dir)

  fun toString f =
    fn ID => "id"
     | ID_ABS => "id-abs"
     | BOOL => "bool"
     | BOOL_TT => "tt"
     | BOOL_FF => "ff"
     | BOOL_HCOM (extents, dir) =>
         "hcom-bool["
           ^ ListSpine.pretty f "," extents
           ^ "]{"
           ^ DimSpan.toString f dir
           ^ "}"

  local
    structure J = Json
    open OptionUtil
    infix **
  in
    fun encode f =
      fn ID => J.String "id"
       | ID_ABS => J.String "id-abs"
       | BOOL => J.String "bool"
       | BOOL_TT => J.String "bool-tt"
       | BOOL_FF => J.String "bool-ff"
       | BOOL_HCOM (extents, dir) => J.Obj [("hcom-bool", J.Obj [("extents", J.Array (List.map f extents)), ("dir", DimSpan.encode f dir)])]

    fun decode f =
      fn J.String "id" => SOME ID
       | J.String "id-abs" => SOME ID_ABS
       | J.String "bool" => SOME BOOL
       | J.String "bool-tt" => SOME BOOL_TT
       | J.String "bool-ff" => SOME BOOL_FF
       | J.Obj [("hcom-bool", J.Obj [("extents", J.Array es), ("dir", s)])] => Option.map BOOL_HCOM (traverseOpt f es ** DimSpan.decode f s)
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
     | HCOM (extents, dir) => HcomUtil.hcomArity extents
     | ID_APP _ => [] ->> EXP
     | BOOL_IF => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP

  val support =
    fn COE dir => DimSpan.support dir
     | HCOM (extents, dir) => List.foldl (fn (r, xs) => Dim.support r @ xs) (DimSpan.support dir) extents
     | ID_APP r => Dim.support r
     | BOOL_IF => []

  fun eq f =
    fn (COE s1, COE s2) => DimSpan.eq f (s1, s2)
     | (HCOM (es1, s1), HCOM (es2, s2)) => ListPair.allEq (Dim.eq f) (es1, es2) andalso DimSpan.eq f (s1, s2)
     | (ID_APP r1, ID_APP r2) => Dim.eq f (r1, r2)
     | (BOOL_IF, BOOL_IF) => true
     | _ => false

  fun map f =
    fn COE s => COE (DimSpan.map f s)
     | HCOM (es, s) => HCOM (List.map (Dim.map f) es, DimSpan.map f s)
     | ID_APP r => ID_APP (Dim.map f r)
     | BOOL_IF => BOOL_IF

  fun toString f =
    fn COE s => "coe[" ^ DimSpan.toString f s ^ "]"
     | HCOM (es, s) =>
         "hcom["
           ^ ListSpine.pretty (Dim.toString f) "," es
           ^ "]{"
           ^ DimSpan.toString f s
           ^ "}"
     | ID_APP r => "id-app[" ^ Dim.toString f r ^ "]"
     | BOOL_IF => "bool-if"

  local
    structure J = Json
    open OptionUtil
    infix **
  in
    fun encode f =
      fn COE s => J.Obj [("coe", DimSpan.encode f s)]
       | HCOM (es, s) => J.Obj [("hcom", J.Obj [("extents", J.Array (List.map (Dim.encode f) es)), ("dir", DimSpan.encode f s)])]
       | ID_APP r => J.Obj [("id-app", Dim.encode f r)]
       | BOOL_IF => J.String "bool-if"

    fun decode f =
      fn J.Obj [("coe", s)] => Option.map COE (DimSpan.decode f s)
       | J.Obj [("hcom", J.Obj [("extents", J.Array es), ("dir", s)])] => Option.map HCOM (traverseOpt (Dim.decode f) es ** DimSpan.decode f s)
       | J.Obj [("id-app", r)] => Option.map ID_APP (Dim.decode f r)
       | J.String "bool-if" => SOME BOOL_IF
       | _ => NONE
  end

  val input =
    fn COE _ => ([DIM], EXP)
     | HCOM _ => ([], EXP)
     | ID_APP _ => ([], EXP)
     | BOOL_IF => ([], EXP)
end
