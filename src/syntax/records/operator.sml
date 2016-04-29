structure RecordOperatorData =
struct
  datatype 'i rcd_operator =
      RECORD of 'i
    | CONS of 'i
    | PROJ of 'i
end

structure RecordOperator : OPERATOR =
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
       | CONS lbl =>
           [[] * [] <> EXP,
            [] * [] <> EXP]
             ->> EXP
       | PROJ lbl =>
           [[] * [] <> EXP]
             ->> EXP
  end

  val support =
    fn RECORD lbl => [(lbl, SortData.RCD_LBL)]
     | CONS lbl => [(lbl, SortData.RCD_LBL)]
     | PROJ lbl => [(lbl, SortData.RCD_LBL)]

  fun eq f =
    fn (RECORD l1, RECORD l2) => f (l1, l2)
     | (CONS l1, CONS l2) => f (l1, l2)
     | (PROJ l1, PROJ l2) => f (l1, l2)
     | _ => false

  fun toString f =
    fn RECORD lbl => "rcd[" ^ f lbl ^ "]"
     | CONS lbl => "rcons[" ^ f lbl ^ "]"
     | PROJ lbl => "proj[" ^ f lbl ^ "]"

  fun map f =
    fn RECORD lbl => RECORD (f lbl)
     | CONS lbl => CONS (f lbl)
     | PROJ lbl => PROJ (f lbl)
end
