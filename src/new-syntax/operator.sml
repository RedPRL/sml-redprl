structure RedPrlOpData =
struct
  structure P = RedPrlParameterTerm

  datatype sort =
     EXP
   | TAC
   | LVL

  datatype std_operator =
     DFUN | FUN | LAM | AP
   | BOOL | TRUE | FALSE
   | AX

  datatype type_tag =
     TAG_NONE
   | TAG_BOOL
   | TAG_S1
   | TAG_DFUN

  type 'a extents = 'a P.term list
  type 'a span = 'a P.term * 'a P.term

  datatype 'a cubical_operator =
     S1 | BASE | LOOP of 'a P.term
   | HCOM of type_tag * 'a extents * 'a span
   | COE of type_tag * 'a span

  datatype 'a operator =
     STD of std_operator
   | CUB of 'a cubical_operator
end

structure RedPrlSort : ABT_SORT =
struct
  open RedPrlOpData

  type t = sort
  val eq : t * t -> bool = op=

  val toString =
    fn EXP => "exp"
     | TAC => "tac"
     | LVL => "lvl"
end

structure RedPrlArity = ListAbtArity (structure PS = RedPrlParamSort and S = RedPrlSort)

structure ArityNotation =
struct
  fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
  fun op<> (a, b) = (a, b) (* valence *)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure RedPrlOperator : ABT_OPERATOR =
struct
  structure Ar = RedPrlArity

  open RedPrlParamData RedPrlOpData
  open ArityNotation infix <> ->>

  type 'a t = 'a operator

  val arityStd =
    fn DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
     | FUN => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | LAM => [[] * [EXP] <> EXP] ->> EXP
     | AP => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | BOOL => [] ->> EXP
     | TRUE => [] ->> EXP
     | FALSE => [] ->> EXP
     | AX => [] ->> EXP

  local
    val typeArgsForTag =
      fn TAG_NONE => [[] * [] <> EXP]
       | TAG_BOOL => []
       | TAG_S1 => []
       | TAG_DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP]

    fun arityHcom (tag, extents, span) =
      let
        val typeArgs = typeArgsForTag tag
        val capArg = [] * [] <> EXP
        val tubeArgs =
          ListMonad.bind
            (fn _ => [[DIM] * [] <> EXP, [DIM] * [] <> EXP])
            extents
      in
        typeArgs @ capArg :: tubeArgs ->> EXP
      end

    fun arityCoe (tag, span) =
      let
        val typeArgs =
          List.map
            (fn ((_, sigmas),tau) => [DIM] * sigmas <> tau)
            (typeArgsForTag tag)
      in
        typeArgs @ [[] * [] <> EXP] ->> EXP
      end
  in
    val arityCub =
      fn S1 => [] ->> EXP
       | BASE => [] ->> EXP
       | LOOP _ => [] ->> EXP
       | HCOM hcom => arityHcom hcom
       | COE coe => arityCoe coe
  end

  val arity =
    fn STD th => arityStd th
     | CUB th => arityCub th

  val support =
    fn STD th => raise Match
     | CUB th => raise Match

  fun eq f =
    fn (STD th1, STD th2) => th1 = th2
     | (CUB th1, CUB th2) => raise Match
     | _ => false

  fun toString f =
    fn STD th => raise Match
     | CUB th => raise Match

  fun map f =
    fn STD th => raise Match
     | CUB th => raise Match


end

