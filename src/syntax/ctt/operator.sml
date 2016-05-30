structure CttOperators =
struct
  structure Sort = RedPRLAtomicSort
  
  datatype ctt_value =
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
    | DFUN | LAM
    | DEP_ISECT
    | VOID

  datatype ctt_def =
     NOT | FUN

  datatype ctt_cont =
     AP
   | DFUN_DOM
   | DFUN_COD
   | UNIV_GET_LVL
end

structure CttSimpleV =
struct
  open CttOperators
  structure Ar = RedPRLAtomicArity and Sort = RedPRLAtomicSort
  type t = ctt_value

  open SortData ArityNotation
  infix 5 <> ->>

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
     | LAM =>
         [[] * [EXP] <> EXP]
           ->> EXP
     | DEP_ISECT =>
         [[] * [] <> EXP,
          [] * [EXP] <> EXP]
           ->> EXP
     | VOID =>
         [] ->> EXP

  val eq : t * t -> bool = op=

  val toString =
    fn CAPPROX tau => "<={" ^ Sort.toString tau ^ "}"
     | CEQUIV tau => "~{" ^ Sort.toString tau ^ "}"
     | BASE tau => "Base{" ^ Sort.toString tau ^ "}"
     | TOP tau => "Top{" ^ Sort.toString tau ^ "}"
     | EQ tau => "={" ^ Sort.toString tau ^ "}"
     | MEMBER tau => "member{" ^ Sort.toString tau ^ "}"
     | AX => "Ax"
     | UNIV tau => "Univ{" ^ Sort.toString tau ^ "}"
     | SQUASH tau => "Squash{" ^ Sort.toString tau ^ "}"
     | ENSEMBLE (tau1, tau2) => "Ensemble{" ^ Sort.toString tau1 ^ ", " ^ Sort.toString tau2 ^ "}"
     | DFUN => "dfun"
     | LAM => "lam"
     | DEP_ISECT => "disect"
     | VOID => "Void"
end

structure CttSimpleD : ABT_SIMPLE_OPERATOR =
struct
  structure Ar = RedPRLAtomicArity
  open CttOperators

  type t = ctt_def

  open SortData ArityNotation
  infix 5 <> ->>

  val arity =
    fn NOT => [[] * [] <> EXP] ->> EXP
     | FUN => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP

  val eq : t * t -> bool = op=

  val toString =
    fn NOT => "not"
     | FUN => "fun"
end

structure CttSimpleK : ABT_SIMPLE_OPERATOR =
struct
  structure Ar = RedPRLAtomicArity

  open CttOperators
  type t = ctt_cont

  open SortData ArityNotation
  infix 5 <> ->>

  val arity =
    fn AP => [[] * [] <> EXP] ->> EXP
     | DFUN_DOM => [] ->> EXP
     | DFUN_COD => [[] * [] <> EXP] ->> EXP
     | UNIV_GET_LVL => [] ->> LVL

  val eq : t * t -> bool = op=

  val toString =
    fn AP => "ap"
     | DFUN_DOM => "dfun-dom"
     | DFUN_COD => "dfun-cod"
     | UNIV_GET_LVL => "univ-get-lvl"
end

structure CttV = AbtSimpleOperator (CttSimpleV)
structure CttK = AbtSimpleOperator (CttSimpleK)
structure CttD = AbtSimpleOperator (CttSimpleD)
