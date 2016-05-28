structure RecordOperatorData =
struct
  datatype 'i rcd_operator =
      RECORD of 'i
    | SINGL of 'i
    | CONS of 'i
    | PROJ of 'i
    | SINGL_GET_TY
end

structure RecordOperator : ABT_OPERATOR =
struct
  open RecordOperatorData
  structure Arity = Arity
  type 'i t = 'i rcd_operator

  local
    open SortData
    fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun op<> (a, b) = (a, b) (* valence *)
    fun op->> (a, b) = (a, b) (* arity *)
    infix 5 <> ->>
    infix 6 * ^
  in
    val arity =
      fn RECORD lbl =>
           [[] * [] <> EXP,
            [] * [EXP] <> EXP]
             ->> EXP
       | SINGL lbl =>
           [[] * [] <> EXP]
             ->> EXP
       | CONS lbl =>
           [[] * [] <> EXP,
            [] * [] <> EXP]
             ->> EXP
       | PROJ lbl =>
           [[] * [] <> EXP]
             ->> EXP
       | SINGL_GET_TY =>
           [[] * [] <> EXP]
             ->> EXP
  end

  val support =
    fn RECORD lbl => [(lbl, SortData.RCD_LBL)]
     | SINGL lbl => [(lbl, SortData.RCD_LBL)]
     | CONS lbl => [(lbl, SortData.RCD_LBL)]
     | PROJ lbl => [(lbl, SortData.RCD_LBL)]
     | SINGL_GET_TY => []

  fun eq f =
    fn (RECORD l1, RECORD l2) => f (l1, l2)
     | (SINGL l1, SINGL l2) => f (l1, l2)
     | (CONS l1, CONS l2) => f (l1, l2)
     | (PROJ l1, PROJ l2) => f (l1, l2)
     | (SINGL_GET_TY, SINGL_GET_TY) => true
     | _ => false

  fun toString f =
    fn RECORD lbl => "rcd[" ^ f lbl ^ "]"
     | SINGL lbl => "singl[" ^ f lbl ^ "]"
     | CONS lbl => "rcons[" ^ f lbl ^ "]"
     | PROJ lbl => "proj[" ^ f lbl ^ "]"
     | SINGL_GET_TY => "singl-get-ty"

  fun map f =
    fn RECORD lbl => RECORD (f lbl)
     | SINGL lbl => SINGL (f lbl)
     | CONS lbl => CONS (f lbl)
     | PROJ lbl => PROJ (f lbl)
     | SINGL_GET_TY => SINGL_GET_TY
end
