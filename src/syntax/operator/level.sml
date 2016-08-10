structure LevelOperators =
struct
  datatype level_cont =
      LSUP0
    | LSUP1 of int
    | LSUCC
end

structure SimpleLevelV : ABT_SIMPLE_OPERATOR =
struct
  open LevelOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type t = int

  infix <> ->>
  fun arity _ = [] ->> LVL

  val eq : t * t -> bool = op=
  val toString = Int.toString
end

structure SimpleLevelK : ABT_SIMPLE_OPERATOR =
struct
  open LevelOperators SortData ArityNotation
  structure Ar = RedPrlAtomicArity

  type t = level_cont

  infix <> ->>
  val arity =
    fn LSUP0 => [[] * [] <> LVL] ->> LVL
     | LSUP1 _ => [] ->> LVL
     | LSUCC => [] ->> LVL

  val eq : t * t -> bool = op=

  val toString =
    fn LSUP0 => "lsup0"
     | LSUP1 i => "lsup1{" ^ Int.toString i ^ "}"
     | LSUCC => "lsucc"
end

structure LevelV : JSON_ABT_OPERATOR =
struct
  local
    structure O = AbtSimpleOperator (SimpleLevelV)
    structure J = Json and S = RedPrlAtomicSortJson
    open LevelOperators
  in
    open O

    fun encode f i = J.Obj [("lvl", J.Int i)]

    fun decode f =
      fn J.Obj [("lvl", J.Int i)] => SOME i
       | _ => NONE
  end
end

structure LevelK :
sig
  include JSON_ABT_OPERATOR
  val input : 'i t -> RedPrlAtomicArity.sort list * RedPrlAtomicArity.sort
end =
struct
  structure O = AbtSimpleOperator (SimpleLevelK)
  open O SortData LevelOperators

  val input =
    fn LSUP0 => ([], LVL)
     | LSUP1 _ => ([], LVL)
     | LSUCC => ([], LVL)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn LSUP0 => J.String "lsup0"
     | LSUP1 i => J.Obj [("lsup1", J.Int i)]
     | LSUCC => J.String "lsucc"

  fun decode f =
    fn J.String "lsup0" => SOME LSUP0
     | J.Obj [("lsup1", J.Int i)] => SOME (LSUP1 i)
     | J.String "lsucc" => SOME LSUCC
     | _ => NONE
end
