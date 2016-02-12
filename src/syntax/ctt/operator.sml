structure CttOperatorData =
struct
  datatype ctt_operator =
      CAPPROX of Sort.t
    | CEQUIV of Sort.t
    | BASE of Sort.t
    | UNIV of Sort.t
    | EQ of Sort.t
    | MEMBER of Sort.t
    | AX
    | SQUASH of Sort.t
    | SPECIES of Sort.t * Sort.t
end

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
       | BASE tau =>
           [] ->> EXP
       | EQ tau =>
           [[] * [] <> tau,
            [] * [] <> tau,
            [] * [] <> EXP]
             ->> EXP
       | MEMBER tau =>
           [[] * [] <> tau,
            [] * [] <> EXP]
             ->> EXP
       | UNIV tau =>
           [[] * [] <> LVL]
             ->> EXP
       | AX =>
           [] ->> EXP
       | SQUASH tau =>
           [[] * [] <> EXP]
             ->> EXP
       | SPECIES (tau, _) =>
           [[] * [] <> EXP,
            [] * [tau] <> EXP]
             ->> EXP
  end

  val eq : t * t -> bool = op=

  val toString =
    fn CAPPROX tau =>
         "<={" ^ Sort.toString tau ^ "}"
     | CEQUIV tau =>
         "~{" ^ Sort.toString tau ^ "}"
     | BASE tau =>
         "Base{" ^ Sort.toString tau ^ "}"
     | EQ tau =>
         "={" ^ Sort.toString tau ^ "}"
     | MEMBER tau =>
         "member{" ^ Sort.toString tau ^ "}"
     | AX =>
         "Ax"
     | UNIV tau =>
         "Univ{" ^ Sort.toString tau ^ "}"
     | SQUASH tau =>
         "Squash{" ^ Sort.toString tau ^ "}"
     | SPECIES (tau1, tau2) =>
         "Species{" ^ Sort.toString tau1 ^ ", " ^ Sort.toString tau2 ^ "}"
end

structure CttOperator = SimpleOperator (CttSimpleOperator)
