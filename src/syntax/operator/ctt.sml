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

structure CttV : JSON_ABT_OPERATOR =
struct
  structure O = AbtSimpleOperator (CttSimpleV)
  structure J = Json and S = RedPrlAtomicSortJson

  open O

  local
    open CttOperators
  in
    fun encode f =
      fn CAPPROX tau => J.Obj [("capprox", S.encode tau)]
       | CEQUIV tau => J.Obj [("cequiv", S.encode tau)]
       | BASE tau => J.Obj [("base", S.encode tau)]
       | TOP tau => J.Obj [("top", S.encode tau)]
       | UNIV tau => J.Obj [("univ", S.encode tau)]
       | EQ tau => J.Obj [("eq", S.encode tau)]
       | AX => J.String "ax"
       | SQUASH tau => J.Obj [("squash", S.encode tau)]
       | ENSEMBLE (sigma, tau) => J.Obj [("ensemble", J.Array [S.encode sigma, S.encode tau])]
       | DFUN => J.String "dfun"
       | LAM => J.String "lam"
       | DEP_ISECT => J.String "dep_isect"
       | VOID => J.String "void"
       | DUMMY => J.String "dummy"

    fun decode f =
      fn J.Obj [("capprox", tau)] => Option.map CAPPROX (S.decode tau)
       | J.Obj [("cequiv", tau)] => Option.map CEQUIV (S.decode tau)
       | J.Obj [("base", tau)] => Option.map BASE (S.decode tau)
       | J.Obj [("top", tau)] => Option.map TOP (S.decode tau)
       | J.Obj [("univ", tau)] => Option.map UNIV (S.decode tau)
       | J.Obj [("eq", tau)] => Option.map EQ (S.decode tau)
       | J.String "ax" => SOME AX
       | J.Obj [("squash", tau)] => Option.map SQUASH (S.decode tau)
       | J.Obj [("ensemble", J.Array [sigma, tau])] =>
           (case (S.decode sigma, S.decode tau) of
               (SOME sigma', SOME tau') => SOME (ENSEMBLE (sigma', tau'))
             | _ => NONE)
      | J.String "dfun" => SOME DFUN
      | J.String "lam" => SOME LAM
      | J.String "dep_isect" => SOME DEP_ISECT
      | J.String "void" => SOME VOID
      | J.String "dummy" => SOME DUMMY
      | _ => NONE
  end
end

structure CttD : JSON_ABT_OPERATOR =
struct
  structure O = AbtSimpleOperator (CttSimpleD)
  open O

  local
    structure J = Json and S = RedPrlAtomicSortJson
    open CttOperators
  in
    fun encode f =
      fn NOT => J.String "not"
       | FUN => J.String "fun"
       | MEMBER tau => J.Obj [("member", S.encode tau)]

    fun decode f =
      fn J.String "not" => SOME NOT
       | J.String "FUN" => SOME FUN
       | J.Obj [("member", tau)] => Option.map MEMBER (S.decode tau)
       | _ => NONE
  end
end

structure CttK :
sig
  include JSON_ABT_OPERATOR
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

  local
    structure J = Json and S = RedPrlAtomicSortJson
  in
    fun encode f =
      fn AP => J.String "ap"
       | DFUN_DOM => J.String "dfun_dom"
       | DFUN_COD => J.String "dfun_cod"
       | UNIV_GET_LVL => J.String "univ_get_lvl"
       | FRESH (sigma, tau) => J.Obj [("fresh", J.Array [S.encode sigma, S.encode tau])]
       | FRESH_K ((u, sigma), tau) => J.Obj [("fresh_k", J.Array [f u, S.encode sigma, S.encode tau])]

    fun decode f =
      fn J.String "ap" => SOME AP
       | J.String "dfun_dom" => SOME DFUN_DOM
       | J.String "dfun_cod" => SOME DFUN_COD
       | J.String "univ_get_lvl" => SOME UNIV_GET_LVL
       | J.Obj [("fresh", J.Array [sigma, tau])] =>
           (case (S.decode sigma, S.decode tau) of
               (SOME sigma', SOME tau') => SOME (FRESH (sigma', tau'))
             | _ => NONE)
       | J.Obj [("fresh_k", J.Array [u, sigma, tau])] =>
           (case (f u, S.decode sigma, S.decode tau) of
               (SOME u', SOME sigma', SOME tau') => SOME (FRESH_K ((u', sigma'), tau'))
             | _ => NONE)
       | _ => NONE
  end
end
