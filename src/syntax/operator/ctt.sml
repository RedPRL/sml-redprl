structure CttOperators =
struct
  structure Sort = RedPrlAtomicSort

  datatype ctt_value =
     CAPPROX of Sort.t
   | CEQUIV of Sort.t
   | BASE of Sort.t
   | TOP of Sort.t
   | UNIV of Sort.t
   | EQ of Sort.t
   | AX
   | SQUASH of Sort.t
   | ENSEMBLE of Sort.t * Sort.t
   | DFUN | LAM
   | DEP_ISECT
   | VOID
   | DUMMY (* the single inhabitant of the UNIT sort *)

  datatype ctt_def =
     NOT | FUN | MEMBER of Sort.t

  datatype 'i ctt_cont =
     AP
   | DFUN_DOM
   | DFUN_COD
   | UNIV_GET_LVL

   | FRESH of Sort.t * Sort.t
   | FRESH_K of ('i * Sort.t) * Sort.t
end

structure CttSimpleV =
struct
  open CttOperators
  structure Ar = RedPrlAtomicArity and Sort = RedPrlAtomicSort
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
     | DUMMY =>
         [] ->> UNIT

  val eq : t * t -> bool = op=

  val toString =
    fn CAPPROX tau => "<={" ^ Sort.toString tau ^ "}"
     | CEQUIV tau => "~{" ^ Sort.toString tau ^ "}"
     | BASE tau => "Base{" ^ Sort.toString tau ^ "}"
     | TOP tau => "Top{" ^ Sort.toString tau ^ "}"
     | EQ tau => "={" ^ Sort.toString tau ^ "}"
     | AX => "Ax"
     | UNIV tau => "Univ{" ^ Sort.toString tau ^ "}"
     | SQUASH tau => "Squash{" ^ Sort.toString tau ^ "}"
     | ENSEMBLE (tau1, tau2) => "Ensemble{" ^ Sort.toString tau1 ^ ", " ^ Sort.toString tau2 ^ "}"
     | DFUN => "dfun"
     | LAM => "lam"
     | DEP_ISECT => "disect"
     | VOID => "Void"
     | DUMMY => "*"
end

structure CttSimpleD : ABT_SIMPLE_OPERATOR =
struct
  structure Ar = RedPrlAtomicArity
  open CttOperators

  type t = ctt_def

  open SortData ArityNotation
  infix 5 <> ->>

  val arity =
    fn NOT => [[] * [] <> EXP] ->> EXP
     | FUN => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | MEMBER tau => [[] * [] <> tau, [] * [] <> EXP] ->> EXP

  val eq : t * t -> bool = op=

  val toString =
    fn NOT => "not"
     | FUN => "fun"
     | MEMBER tau => "member{" ^ Sort.toString tau ^ "}"
end

structure CttV = AbtSimpleOperator (CttSimpleV)
structure CttD = AbtSimpleOperator (CttSimpleD)

structure CttK :
sig
  include ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicArity.sort
end =
struct
   open CttOperators SortData

   structure Ar = RedPrlAtomicArity

   open CttOperators
   type 'i t = 'i ctt_cont

   open SortData ArityNotation
   infix 5 <> ->>

   val arity =
     fn AP => [[] * [] <> EXP] ->> EXP
      | DFUN_DOM => [] ->> EXP
      | DFUN_COD => [[] * [] <> EXP] ->> EXP
      | UNIV_GET_LVL => [] ->> LVL
      | FRESH (sigma, tau) => [[sigma] * [] <> tau] ->> tau
      | FRESH_K (_, tau) => [] ->> tau

   val support =
     fn FRESH_K ((u, sigma), _) => [(u, sigma)]
      | _ => []

   fun eq f =
     fn (AP, AP) => true
      | (DFUN_DOM, DFUN_DOM) => true
      | (DFUN_COD, DFUN_COD) => true
      | (UNIV_GET_LVL, UNIV_GET_LVL) => true
      | (FRESH (sigma1, tau1), FRESH (sigma2, tau2)) =>
          sigma1 = sigma2 andalso tau1 = tau2
      | (FRESH_K ((u1, sigma1), tau1), FRESH_K ((u2, sigma2), tau2)) =>
          f (u1, u2) andalso sigma1 = sigma2 andalso tau1 = tau2
      | _ => false

   fun map f =
     fn AP => AP
      | DFUN_DOM => DFUN_DOM
      | DFUN_COD => DFUN_COD
      | UNIV_GET_LVL => UNIV_GET_LVL
      | FRESH (sigma, tau) => FRESH (sigma, tau)
      | FRESH_K ((u, sigma), tau) => FRESH_K ((f u, sigma), tau)

   fun toString f =
     fn AP => "ap"
      | DFUN_DOM => "dfun-dom"
      | DFUN_COD => "dfun-cod"
      | UNIV_GET_LVL => "univ-get-lvl"
      | FRESH _ => "\206\189"
      | FRESH_K ((u, _), _) => "\206\189[" ^ f u ^ "]"

   val input =
     fn AP => EXP
      | DFUN_DOM => EXP
      | DFUN_COD => EXP
      | UNIV_GET_LVL => EXP
      | FRESH (sigma, tau) => UNIT
      | FRESH_K ((u, sigma), tau) => tau
end
