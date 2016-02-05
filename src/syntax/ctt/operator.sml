structure CttSimpleOperator =
struct
  open CttOperatorData

  structure Arity = Arity

  type t = ctt_operator

  local
    open SortData
    fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun op<> (a, b) = (a, b) (* valence *)
    fun op->> (a, b) = (a, b) (* arity *)
    infix 5 <> ->>
    infix 6 * ^
  in
    val arity =
      fn CAPPROX tau =>
           [[] * [] <> tau,
            [] * [] <> tau]
             ->> EXP
       | CEQUIV tau =>
           [[] * [] <> tau,
            [] * [] <> tau]
             ->> EXP
       | AX =>
           [] ->> EXP
  end

  val eq : t * t -> bool = op=

  val toString =
    fn CAPPROX tau =>
         "<={" ^ Sort.toString tau ^ "}"
     | CEQUIV tau =>
         "~{" ^ Sort.toString tau ^ "}"
     | AX =>
         "Ax"
end

structure CttOperator = SimpleOperator (CttSimpleOperator)
