structure RecordOperators =
struct
  datatype 'i rcd_val =
     CONS of 'i
   | SINGL of 'i

  datatype 'i rcd_cont =
     PROJ of 'i
   | SINGL_GET_TY

  datatype 'i rcd_def =
     RECORD of 'i
end

structure RecordV : JSON_ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i rcd_val

  infix <> ->>

  val arity =
    fn CONS lbl => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | SINGL lbl => [[] * [] <> EXP] ->> EXP

  val support =
    fn CONS lbl => [(lbl, RCD_LBL)]
     | SINGL lbl => [(lbl, RCD_LBL)]

  fun eq f =
    fn (CONS l1, CONS l2) => f (l1, l2)
     | (SINGL l1, SINGL l2) => f (l1, l2)
     | _ => false

  fun toString f =
    fn CONS lbl => "rcons[" ^ f lbl ^ "]"
     | SINGL lbl => "rsing[" ^ f lbl ^ "]"

  fun map f =
    fn CONS lbl => CONS (f lbl)
     | SINGL lbl => SINGL (f lbl)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn CONS lbl => J.Obj [("cons", f lbl)]
     | SINGL lbl => J.Obj [("singl", f lbl)]

  fun decode f =
    fn J.Obj [("cons", lbl)] => Option.map CONS (f lbl)
     | J.Obj [("singl", lbl)] => Option.map SINGL (f lbl)
     | _ => NONE
end


structure RecordK :
sig
  include JSON_ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicArity.sort
end =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i rcd_cont

  infix <> ->>

  val arity =
    fn PROJ lbl => [] ->> EXP
     | SINGL_GET_TY => [] ->> EXP

  val input =
    fn PROJ _ => EXP
     | SINGL_GET_TY => EXP

  val support =
    fn PROJ lbl => [(lbl, RCD_LBL)]
     | SINGL_GET_TY => []

  fun eq f =
    fn (PROJ l1, PROJ l2) => f (l1, l2)
     | (SINGL_GET_TY, SINGL_GET_TY) => true
     | _ => false

  fun toString f =
    fn PROJ lbl => "rproj[" ^ f lbl ^ "]"
     | SINGL_GET_TY => "singl-get-ty"

  fun map f =
    fn PROJ lbl => PROJ (f lbl)
     | SINGL_GET_TY => SINGL_GET_TY

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn PROJ lbl => J.Obj [("proj", f lbl)]
     | SINGL_GET_TY => J.String "singl_get_ty"

  fun decode f =
    fn J.Obj [("proj", lbl)] => Option.map PROJ (f lbl)
     | J.String "singl_get_ty" => SOME SINGL_GET_TY
     | _ => NONE
end

structure RecordD : JSON_ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i rcd_def

  infix <> ->>

  fun arity (RECORD lbl) =
    [[] * [] <> EXP,
     [] * [EXP] <> EXP]
       ->> EXP

  fun support (RECORD lbl) =
    [(lbl, RCD_LBL)]

  fun eq  _ _ = true

  fun toString f (RECORD lbl) =
    "rcd[" ^ f lbl ^ "]"

  fun map f (RECORD lbl) =
    RECORD (f lbl)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f (RECORD lbl) =
    J.Obj [("record", f lbl)]

  fun decode f =
    fn J.Obj [("record", lbl)] => Option.map RECORD (f lbl)
     | _ => NONE
end
