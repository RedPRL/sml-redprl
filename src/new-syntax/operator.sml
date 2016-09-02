structure RedPrlSortData =
struct
  datatype sort =
     EXP
   | TAC
   | MTAC
   | THM
end

structure RedPrlSort : ABT_SORT =
struct
  open RedPrlSortData

  type t = sort
  val eq : t * t -> bool = op=

  val toString =
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | THM => "thm"
end

structure RedPrlArity = ListAbtArity (structure PS = RedPrlParamSort and S = RedPrlSort)

structure RedPrlOpData =
struct
  open RedPrlSortData
  structure P = RedPrlParameterTerm

  datatype mono_operator =
     DFUN | FUN | LAM | AP
   | BOOL | TRUE | FALSE
   | S1 | BASE
   | AX
   | CEQ

   | REFINE of bool | EXTRACT

   | TAC_SEQ of int
   | TAC_ID
   | MTAC_ALL | MTAC_EACH of int | MTAC_FOCUS of int

  (* We end up having separate hcom operator for the different types. This
   * corresponds to the fact that there are two stages of computation for a kan
   * composition: first we compute the type argument to a canonical form, and then
   * further computation may proceed on the basis of the shape of that canonical form.
   *
   * To ensure that our operational semantics does not require us to inspect the subterms
   * of an operator application (a "no-no"), we embed the contents of the canonical type form
   * in the arguments of the hcom in case it is known. Therefore, expect to see kan compositions
   * like the following:
   *
   *    1. hcom[TAG_NONE; rs; r ~> r'](ty; cap; tubes...)
   *    2. hcom[TAG_BOOL; rs; r ~> r'](cap; tubes...)
   *    3. hcom[TAG_DFUN; rs; r ~> r'](a; [x].b[x]; cap; tubes...)
   *
   * We use the same approach with coercions, except that we bind a dimension in the type arguments.
   *)

  datatype type_tag =
     TAG_NONE
   | TAG_BOOL
   | TAG_S1
   | TAG_DFUN

  type 'a extents = 'a P.term list
  type 'a dir = 'a P.term * 'a P.term

  datatype 'a poly_operator =
     LOOP of 'a P.term
   | HCOM of type_tag * 'a extents * 'a dir
   | COE of type_tag * 'a dir
   | CUST of 'a * RedPrlArity.t option
   | UNIV of 'a P.term

  (* We split our operator signature into a couple datatypes, because the implementation of
   * some of the 2nd-order signature obligations can be made trivial for "constant" operators,
   * which we call "monomorphic". *)
  datatype 'a operator =
     MONO of mono_operator
   | POLY of 'a poly_operator
end

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

  val arityMono =
    fn DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
     | FUN => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | LAM => [[] * [EXP] <> EXP] ->> EXP
     | AP => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | BOOL => [] ->> EXP
     | TRUE => [] ->> EXP
     | S1 => [] ->> EXP
     | BASE => [] ->> EXP
     | FALSE => [] ->> EXP
     | AX => [] ->> EXP
     | CEQ => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | REFINE true => [[] * [] <> EXP, [] * [] <> TAC, [] * [] <> EXP] ->> THM
     | REFINE false => [[] * [] <> EXP, [] * [] <> TAC] ->> THM
     | EXTRACT => [[] * [] <> THM] ->> EXP
     | TAC_SEQ n =>
         let
           val hyps = List.tabulate (n, fn _ => HYP)
         in
           [[] * [] <> MTAC, hyps * [] <> TAC] ->> TAC
         end
     | TAC_ID => [] ->> TAC
     | MTAC_ALL => [[] * [] <> TAC] ->> MTAC
     | MTAC_EACH n =>
         let
           val tacs = List.tabulate (n, fn _ => [] * [] <> TAC)
         in
           tacs ->> MTAC
         end
     | MTAC_FOCUS i => [[] * [] <> TAC] ->> MTAC

  local
    val typeArgsForTag =
      fn TAG_NONE => [[] * [] <> EXP]
       | TAG_BOOL => []
       | TAG_S1 => []
       | TAG_DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP]

    fun arityHcom (tag, extents, dir) =
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

    fun arityCoe (tag, dir) =
      let
        val typeArgs =
          List.map
            (fn ((_, sigmas),tau) => [DIM] * sigmas <> tau)
            (typeArgsForTag tag)
      in
        typeArgs @ [[] * [] <> EXP] ->> EXP
      end
  in
    val arityPoly =
      fn LOOP _ => [] ->> EXP
       | HCOM hcom => arityHcom hcom
       | COE coe => arityCoe coe
       | CUST (_, ar) => Option.valOf ar
       | UNIV lvl => [] ->> EXP
  end

  val arity =
    fn MONO th => arityMono th
     | POLY th => arityPoly th

  local
    val dimSupport =
      fn P.VAR a => [(a, DIM)]
       | _ => []

    fun spanSupport (r, r') =
      dimSupport r @ dimSupport r'

    val lvlSupport =
      fn P.VAR a => [(a, LVL)]
       | _ => []

  in
    val supportPoly =
      fn LOOP r => dimSupport r
       | HCOM (_, extents, dir) =>
           ListMonad.bind dimSupport extents
             @ spanSupport dir
       | COE (_, dir) => spanSupport dir
       | CUST (opid, _) => [(opid, OPID)]
       | UNIV lvl => lvlSupport lvl
  end

  val support =
    fn MONO th => []
     | POLY th => supportPoly th

  local
    fun spanEq f ((r1, r'1), (r2, r'2)) =
      P.eq f (r1, r2) andalso P.eq f (r'1, r'2)

    fun extentsEq f =
      ListPair.allEq (P.eq f)
  in
    fun eqPoly f =
      fn (LOOP r, LOOP r') => P.eq f (r, r')
       | (HCOM (tag1, exs1, sp1), HCOM (tag2, exs2, sp2)) =>
           tag1 = tag2
             andalso extentsEq f (exs1, exs2)
             andalso spanEq f (sp1, sp2)
       | (COE (tag1, sp1), COE (tag2, sp2)) =>
           tag1 = tag2 andalso spanEq f (sp1, sp2)
       | (CUST (opid1, _), CUST (opid2, _)) =>
           f (opid1, opid2)
       | _ => false
  end

  fun eq f =
    fn (MONO th1, MONO th2) => th1 = th2
     | (POLY th1, POLY th2) => eqPoly f (th1, th2)
     | _ => false

  val toStringMono =
    fn DFUN => "dfun"
     | FUN => "fun"
     | LAM => "lam"
     | AP => "ap"
     | BOOL => "bool"
     | TRUE => "true"
     | FALSE => "false"
     | S1 => "S1"
     | BASE => "base"
     | AX => "ax"
     | CEQ => "ceq"
     | REFINE _ => "refine"
     | EXTRACT => "extract"
     | TAC_SEQ _ => "seq"
     | TAC_ID => "id"
     | MTAC_ALL => "all"
     | MTAC_EACH n => "each"
     | MTAC_FOCUS i => "focus{" ^ Int.toString i ^ "}"


  local
    fun spanToString f (r, r') =
      P.toString f r ^ " ~> " ^ P.toString f r'

    fun extentsToString f =
      ListSpine.pretty (P.toString f) ","

    val tagToString =
      fn TAG_NONE => ""
       | TAG_BOOL => "/bool"
       | TAG_S1 => "/S1"
       | TAG_DFUN => "/dfun"
  in
    fun toStringPoly f =
      fn LOOP r => "loop[" ^ P.toString f r ^ "]"
       | HCOM (tag, extents, dir) =>
           "hcom"
             ^ tagToString tag
             ^ "["
             ^ extentsToString f extents
             ^ "; "
             ^ spanToString f dir
             ^ "]"
       | COE (tag, dir) =>
           "coe"
             ^ tagToString tag
             ^ "["
             ^ spanToString f dir
             ^ "]"
       | CUST (opid, ar) =>
           "cust[" ^ f opid ^ "]"
       | UNIV lvl => "univ{" ^ P.toString f lvl ^ "}"
  end

  fun toString f =
    fn MONO th => toStringMono th
     | POLY th => toStringPoly f th

  local
    fun mapSpan f (r, r') = (P.bind f r, P.bind f r')
    fun mapExtents f = List.map (P.bind f)

    fun mapSym f a =
      case f a of
         P.VAR a' => a'
       | _ => raise Fail "Expected symbol, but got application"

    fun mapLvl f a =
      case f a of
         P.VAR a' => P.VAR a'
       | P.APP (LVL_SUCC a') => P.APP (LVL_SUCC a')
       | _ => raise Fail "Expected level parameter"
  in
    fun mapPoly f =
      fn LOOP r => LOOP (P.bind f r)
       | HCOM (tag, extents, dir) => HCOM (tag, mapExtents f extents, mapSpan f dir)
       | COE (tag, dir) => COE (tag, mapSpan f dir)
       | CUST (opid, ar) => CUST (mapSym f opid, ar)
       | UNIV lvl => UNIV (P.bind (mapLvl f) lvl)
  end

  fun map f =
    fn MONO th => MONO th
     | POLY th => POLY (mapPoly f th)

end
