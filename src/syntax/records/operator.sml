structure RecordOperators =
struct
  datatype 'i rcd_val =
     CONS of 'i

  datatype 'i rcd_cont =
     PROJ of 'i
   | SINGL_GET_TY

  datatype 'i rcd_def =
     RECORD of 'i
end

structure RecordV : ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPRLAtomicArity

  type 'i t = 'i rcd_val

  infix <> ->>

  fun arity (CONS lbl) =
    [[] * [] <> EXP, [] * [] <> EXP] ->> EXP

  fun support (CONS lbl) =
    [(lbl, RCD_LBL)]

  fun eq  _ _ = true

  fun toString f (CONS lbl) =
    "rcons[" ^ f lbl ^ "]"

  fun map f (CONS lbl) =
    CONS (f lbl)
end

structure RecordK : ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPRLAtomicArity

  type 'i t = 'i rcd_cont

  infix <> ->>

  val arity =
    fn PROJ lbl => [] ->> EXP
     | SINGL_GET_TY => [] ->> EXP

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
end

structure RecordD : ABT_OPERATOR =
struct
  open RecordOperators ArityNotation SortData
  structure Ar = RedPRLAtomicArity

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
end
