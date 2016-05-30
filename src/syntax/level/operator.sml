structure LevelOperators =
struct
  datatype level_value =
      LBASE
    | LSUCC

  datatype level_cont =
      LSUP0
    | LSUP1
    | LSUCC_K
end

structure SimpleLevelV : ABT_SIMPLE_OPERATOR =
struct
  open LevelOperators SortData ArityNotation
  structure Ar = RedPRLAtomicArity

  type t = level_value

  infix <> ->>
  val arity =
    fn LBASE => [] ->> LVL
     | LSUCC => [[] * [] <> LVL] ->> LVL

  val eq : t * t -> bool = op=

  val toString =
    fn LBASE => "lbase"
     | LSUCC => "lsucc"
end

structure SimpleLevelK : ABT_SIMPLE_OPERATOR =
struct
  open LevelOperators SortData ArityNotation
  structure Ar = RedPRLAtomicArity

  type t = level_cont

  infix <> ->>
  val arity =
    fn LSUP0 => [[] * [] <> LVL] ->> LVL
     | LSUP1 => [[] * [] <> LVL] ->> LVL
     | LSUCC_K => [] ->> LVL

  val eq : t * t -> bool = op=

  val toString =
    fn LSUP0 => "lsup0"
     | LSUP1 => "lsup1"
     | LSUCC_K => "lsucc!"
end

structure LevelV = AbtSimpleOperator (SimpleLevelV)
structure LevelK = AbtSimpleOperator (SimpleLevelK)
