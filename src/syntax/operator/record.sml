structure RecordOperators =
struct
  datatype 'i rcd_val =
     CONS of 'i
   | RECORD of 'i

  datatype 'i rcd_cont =
     PROJ of 'i
   | PROJ_TY of 'i

  datatype 'i rcd_def =
     SINGL of 'i

end

structure RecordV : JSON_ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i rcd_val

  infix <> ->>

  val arity =
    fn CONS lbl => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | RECORD lbl => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP

  val support =
    fn CONS lbl => [(lbl, RCD_LBL)]
     | RECORD lbl => [(lbl, RCD_LBL)]

  fun eq f =
    fn (CONS l1, CONS l2) => f (l1, l2)
     | (RECORD l1, RECORD l2) => f (l1, l2)
     | _ => false

  fun toString f =
    fn CONS lbl => "rcons[" ^ f lbl ^ "]"
     | RECORD lbl => "rcd[" ^ f lbl ^ "]"

  fun map f =
    fn CONS lbl => CONS (f lbl)
     | RECORD lbl => RECORD (f lbl)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn CONS lbl => J.Obj [("cons", f lbl)]
     | RECORD lbl => J.Obj [("rcd", f lbl)]

  fun decode f =
    fn J.Obj [("cons", lbl)] => Option.map CONS (f lbl)
     | J.Obj [("rcd", lbl)] => Option.map RECORD (f lbl)
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
     | PROJ_TY lbl => [[] * [] <> EXP] ->> EXP

  val input =
    fn PROJ _ => EXP
     | PROJ_TY _ => EXP

  val support =
    fn PROJ lbl => [(lbl, RCD_LBL)]
     | PROJ_TY lbl => [(lbl, RCD_LBL)]

  fun eq f =
    fn (PROJ l1, PROJ l2) => f (l1, l2)
     | (PROJ_TY l1, PROJ_TY l2) => f (l1, l2)
     | _ => false


  fun toString f =
    fn PROJ lbl => "rproj[" ^ f lbl ^ "]"
     | PROJ_TY lbl => "rproj-ty[" ^ f lbl ^ "]"

  fun map f =
    fn PROJ lbl => PROJ (f lbl)
     | PROJ_TY lbl => PROJ_TY (f lbl)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn PROJ lbl => J.Obj [("proj", f lbl)]
     | PROJ_TY lbl => J.Obj [("proj-ty", f lbl)]

  fun decode f =
    fn J.Obj [("proj", lbl)] => Option.map PROJ (f lbl)
     | J.Obj [("proj-ty", lbl)] => Option.map PROJ_TY (f lbl)
     | _ => NONE
end

structure RecordD : JSON_ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPrlAtomicArity

  type 'i t = 'i rcd_def

  infix <> ->>

  fun arity (SINGL lbl) = [[] * [] <> EXP] ->> EXP

  fun support (SINGL lbl) =
    [(lbl, RCD_LBL)]

  fun eq  _ _ = true

  fun toString f (SINGL lbl) =
    "singl[" ^ f lbl ^ "]"

  fun map f (SINGL lbl) =
    SINGL (f lbl)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f (SINGL lbl) =
    J.Obj [("singl", f lbl)]

  fun decode f =
    fn J.Obj [("singl", lbl)] => Option.map SINGL (f lbl)
     | _ => NONE
end
