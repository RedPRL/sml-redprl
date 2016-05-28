structure CttOperatorData =
struct
  datatype ctt_operator =
      CAPPROX of Sort.t
    | CEQUIV of Sort.t
    | BASE of Sort.t
    | TOP of Sort.t
    | UNIV of Sort.t
    | EQ of Sort.t
    | MEMBER of Sort.t
    | AX
    | SQUASH of Sort.t
    | ENSEMBLE of Sort.t * Sort.t
    | DFUN | FUN | LAM | AP
    | DEP_ISECT
    | VOID | NOT
    | DFUN_DOM | DFUN_COD | UNIV_GET_LVL
    | NU of Sort.t * Sort.t
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
       | TOP tau =>
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
       | ENSEMBLE (tau, _) =>
           [[] * [] <> EXP,
            [] * [tau] <> EXP]
             ->> EXP
       | DFUN =>
           [[] * [] <> EXP,
            [] * [EXP] <> EXP]
             ->> EXP
       | FUN =>
           [[] * [] <> EXP,
            [] * [] <> EXP]
             ->> EXP
       | LAM =>
           [[] * [EXP] <> EXP]
             ->> EXP
       | AP =>
           [[] * [] <> EXP,
            [] * [] <> EXP]
             ->> EXP
       | DEP_ISECT =>
           [[] * [] <> EXP,
            [] * [EXP] <> EXP]
             ->> EXP
       | VOID =>
           [] ->> EXP
       | NOT =>
           [[] * [] <> EXP]
             ->> EXP
       | DFUN_DOM =>
           [[] * [] <> EXP]
             ->> EXP
       | DFUN_COD =>
           [[] * [] <> EXP,
            [] * [] <> EXP]
             ->> EXP
       | UNIV_GET_LVL =>
           [[] * [] <> EXP]
             ->> LVL
       | NU (sigma, tau) =>
           [[sigma] * [] <> tau]
             ->> tau
  end

  val eq : t * t -> bool = op=

  val toString =
    fn CAPPROX tau =>
         "<={" ^ Sort.toString tau ^ "}"
     | CEQUIV tau =>
         "~{" ^ Sort.toString tau ^ "}"
     | BASE tau =>
         "Base{" ^ Sort.toString tau ^ "}"
     | TOP tau =>
         "Top{" ^ Sort.toString tau ^ "}"
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
     | ENSEMBLE (tau1, tau2) =>
         "Ensemble{" ^ Sort.toString tau1 ^ ", " ^ Sort.toString tau2 ^ "}"
     | DFUN =>
         "dfun"
     | FUN =>
         "fun"
     | LAM =>
         "lam"
     | AP =>
         "ap"
     | DEP_ISECT =>
         "disect"
     | VOID =>
         "Void"
     | NOT =>
         "not"
     | DFUN_DOM =>
         "dfun-dom"
     | DFUN_COD =>
         "dfun-cod"
     | UNIV_GET_LVL =>
         "univ-get-lvl"
     | NU (sigma, tau) =>
         "nu{" ^ Sort.toString sigma ^ "," ^ Sort.toString tau ^ "}"
end

structure CttOperator = AbtSimpleOperator (CttSimpleOperator)
