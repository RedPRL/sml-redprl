structure RecordOperatorData =
struct
  datatype 'i rcd_operator =
      DESC_NIL
    | DESC_CONS of 'i
    | NIL
    | CONS of 'i
    | PROJ of 'i
    | RECORD
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
      fn DESC_NIL =>
           [] ->> RCD_DESC
       | DESC_CONS lbl =>
           [[] * [] <> EXP,
            [] * [EXP] <> RCD_DESC]
             ->> RCD_DESC
       | NIL =>
           [] ->> EXP
       | CONS lbl =>
           [[] * [] <> EXP,
            [] * [] <> EXP]
             ->> EXP
       | PROJ lbl =>
           [[] * [] <> EXP]
             ->> EXP
       | RECORD =>
           [[] * [] <> RCD_DESC]
             ->> EXP

  end

  val support =
    fn DESC_NIL => []
     | DESC_CONS lbl => [(lbl, SortData.RCD_LBL)]
     | NIL => []
     | CONS lbl => [(lbl, SortData.RCD_LBL)]
     | PROJ lbl => [(lbl, SortData.RCD_LBL)]
     | RECORD => []

  fun eq f =
    fn (DESC_NIL, DESC_NIL) => true
     | (DESC_CONS l1, DESC_CONS l2) => f (l1, l2)
     | (NIL, NIL) => true
     | (CONS l1, CONS l2) => f (l1, l2)
     | (PROJ l1, PROJ l2) => f (l1, l2)
     | (RECORD, RECORD) => true
     | _ => false

  fun toString f =
    fn DESC_NIL => "rdesc-nil"
     | DESC_CONS lbl => "rdesc-cons[" ^ f lbl ^ "]"
     | NIL => "rnil"
     | CONS lbl => "rcons[" ^ f lbl ^ "]"
     | PROJ lbl => "proj[" ^ f lbl ^ "]"
     | RECORD => "record"

  fun map f =
    fn DESC_NIL => DESC_NIL
     | DESC_CONS lbl => DESC_CONS (f lbl)
     | NIL => NIL
     | CONS lbl => CONS (f lbl)
     | PROJ lbl => PROJ (f lbl)
     | RECORD => RECORD
end
