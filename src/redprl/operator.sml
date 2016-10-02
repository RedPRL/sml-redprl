structure RedPrlSortData =
struct
  datatype sort =
     EXP
   | TAC
   | MTAC
   | THM of sort
   | JDG
   | TRIV
end

structure RedPrlSort : ABT_SORT =
struct
  open RedPrlSortData

  type t = sort
  val eq : t * t -> bool = op=

  val rec toString =
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | THM sort => "thm{" ^ toString sort ^ "}"
     | JDG => "jdg"
     | TRIV => "triv"
end

structure RedPrlArity = ListAbtArity (structure PS = RedPrlParamSort and S = RedPrlSort)

structure RedPrlOpData =
struct
  open RedPrlSortData
  structure P = RedPrlParameterTerm
  type psort = RedPrlParamData.param_sort

  datatype mono_operator =
     DFUN | LAM | AP
   | DPROD | PAIR | FST | SND
   | BOOL | TRUE | FALSE | IF
   | S1 | BASE | S1_ELIM
   | AX
   | ID_TY | ID_ABS

   | REFINE of bool * sort | EXTRACT of sort

   (* primitive tacticals and multitacticals *)
   | TAC_SEQ of psort list | TAC_ORELSE | TAC_REC | TAC_PROGRESS
   | MTAC_ALL | MTAC_EACH of int | MTAC_FOCUS of int

   (* primitive rules *)
   | RULE_ID | RULE_EVAL_GOAL | RULE_CEQUIV_REFL | RULE_AUTO | RULE_AUTO_STEP | RULE_SYMMETRY | RULE_WITNESS | RULE_HEAD_EXP
   | RULE_CUT | RULE_LEMMA of bool * sort

   (* development calculus terms *)
   | DEV_FUN_INTRO | DEV_PATH_INTRO | DEV_DPROD_INTRO
   | DEV_LET

   | JDG_EQ | JDG_CEQ | JDG_MEM | JDG_TRUE | JDG_TYPE | JDG_EQ_TYPE | JDG_SYNTH

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
   | TAG_DPROD

  type psort = RedPrlArity.Vl.PS.t
  type 'a extents = 'a P.term list
  type 'a dir = 'a P.term * 'a P.term

  datatype 'a poly_operator =
     LOOP of 'a P.term
   | HCOM of type_tag * 'a extents * 'a dir
   | COE of type_tag * 'a dir
   | CUST of 'a * ('a P.term * psort option) list * RedPrlArity.t option
   | UNIV of 'a P.term
   | ID_AP of 'a P.term
   | HYP_REF of 'a
   | RULE_HYP of 'a
   | RULE_ELIM of 'a
   | DEV_BOOL_ELIM of 'a
   | DEV_S1_ELIM of 'a
   | DEV_DFUN_ELIM of 'a

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
     | LAM => [[] * [EXP] <> EXP] ->> EXP
     | AP => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | DPROD => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
     | PAIR => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | FST => [[] * [] <> EXP] ->> EXP
     | SND => [[] * [] <> EXP] ->> EXP
     | BOOL => [] ->> EXP
     | TRUE => [] ->> EXP
     | FALSE => [] ->> EXP
     | IF => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | S1 => [] ->> EXP
     | BASE => [] ->> EXP
     | S1_ELIM => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP, [DIM] * [] <> EXP] ->> EXP
     | AX => [] ->> TRIV
     | ID_TY => [[DIM] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | ID_ABS => [[DIM] * [] <> EXP] ->> EXP
     | REFINE (true, tau) => [[] * [] <> JDG, [] * [] <> TAC, [] * [] <> tau] ->> THM tau
     | REFINE (false, tau) => [[] * [] <> JDG, [] * [] <> TAC] ->> THM tau
     | EXTRACT tau => [[] * [] <> THM tau] ->> tau
     | TAC_SEQ psorts => [[] * [] <> MTAC, psorts * [] <> TAC] ->> TAC
     | TAC_ORELSE => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
     | TAC_REC => [[] * [TAC] <> TAC] ->> TAC
     | TAC_PROGRESS => [[] * [] <> TAC] ->> TAC
     | RULE_ID => [] ->> TAC
     | RULE_AUTO => [] ->> TAC
     | RULE_AUTO_STEP => [] ->> TAC
     | RULE_SYMMETRY => [] ->> TAC
     | RULE_WITNESS => [[] * [] <> EXP] ->> TAC
     | RULE_HEAD_EXP => [] ->> TAC
     | RULE_CUT => [[] * [] <> JDG] ->> TAC
     | RULE_LEMMA (_, tau) => [[] * [] <> THM tau] ->> TAC
     | RULE_EVAL_GOAL => [] ->> TAC
     | RULE_CEQUIV_REFL => [] ->> TAC

     | DEV_FUN_INTRO => [[HYP] * [] <> TAC] ->> TAC
     | DEV_PATH_INTRO => [[DIM] * [] <> TAC] ->> TAC
     | DEV_DPROD_INTRO => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
     | DEV_LET => [[] * [] <> JDG, [] * [] <> TAC, [HYP] * [] <> TAC] ->> TAC

     | MTAC_ALL => [[] * [] <> TAC] ->> MTAC
     | MTAC_EACH n =>
         let
           val tacs = List.tabulate (n, fn _ => [] * [] <> TAC)
         in
           tacs ->> MTAC
         end
     | MTAC_FOCUS i => [[] * [] <> TAC] ->> MTAC
     | JDG_EQ => [[] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> JDG
     | JDG_CEQ => [[] * [] <> EXP, [] * [] <> EXP] ->> JDG
     | JDG_MEM => [[] * [] <> EXP, [] * [] <> EXP] ->> JDG
     | JDG_TRUE => [[] * [] <> EXP] ->> JDG
     | JDG_TYPE => [[] * [] <> EXP] ->> JDG
     | JDG_EQ_TYPE => [[] * [] <> EXP, [] * [] <> EXP] ->> JDG
     | JDG_SYNTH => [[] * [] <> EXP] ->> JDG

  local
    val typeArgsForTag =
      fn TAG_NONE => [[] * [] <> EXP]
       | TAG_BOOL => []
       | TAG_S1 => []
       | TAG_DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP]
       | TAG_DPROD => [[] * [] <> EXP, [] * [EXP] <> EXP]

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
       | CUST (_, _, ar) => Option.valOf ar
       | UNIV lvl => [] ->> EXP
       | ID_AP r => [[] * [] <> EXP] ->> EXP
       | HYP_REF a => [] ->> EXP
       | RULE_HYP a => [] ->> TAC
       | RULE_ELIM a => [] ->> TAC
       | DEV_BOOL_ELIM a => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
       | DEV_S1_ELIM a => [[] * [] <> TAC, [DIM] * [] <> TAC] ->> TAC
       | DEV_DFUN_ELIM a => [[] * [] <> TAC, [HYP,HYP] * [] <> TAC] ->> TAC
  end

  val arity =
    fn MONO th => arityMono th
     | POLY th => arityPoly th

  local
    val dimSupport =
      fn P.VAR a => [(a, DIM)]
       | P.APP t => P.freeVars t

    fun spanSupport (r, r') =
      dimSupport r @ dimSupport r'

    val lvlSupport =
      fn P.VAR a => [(a, LVL)]
       | P.APP t => P.freeVars t

    fun paramsSupport ps =
      ListMonad.bind
        (fn (P.VAR a, SOME tau) => [(a, tau)]
          | (P.VAR a, NONE) => raise Fail "Encountered unannotated parameter in custom operator"
          | (P.APP t, tau) => P.freeVars t)
        ps

  in
    val supportPoly =
      fn LOOP r => dimSupport r
       | HCOM (_, extents, dir) =>
           ListMonad.bind dimSupport extents
             @ spanSupport dir
       | COE (_, dir) => spanSupport dir
       | CUST (opid, ps, _) => (opid, OPID) :: paramsSupport ps
       | UNIV lvl => lvlSupport lvl
       | ID_AP r => dimSupport r
       | HYP_REF a => [(a, HYP)]
       | RULE_HYP a => [(a, HYP)]
       | RULE_ELIM a => [(a, HYP)]
       | DEV_BOOL_ELIM a => [(a, HYP)]
       | DEV_S1_ELIM a => [(a, HYP)]
       | DEV_DFUN_ELIM a => [(a, HYP)]
  end

  val support =
    fn MONO th => []
     | POLY th => supportPoly th

  local
    fun spanEq f ((r1, r'1), (r2, r'2)) =
      P.eq f (r1, r2) andalso P.eq f (r'1, r'2)

    fun extentsEq f =
      ListPair.allEq (P.eq f)

    fun paramsEq f =
      ListPair.allEq (fn ((p, _), (q, _)) => P.eq f (p, q))
  in
    fun eqPoly f =
      fn (LOOP r, LOOP r') => P.eq f (r, r')
       | (HCOM (tag1, exs1, sp1), HCOM (tag2, exs2, sp2)) =>
           tag1 = tag2
             andalso extentsEq f (exs1, exs2)
             andalso spanEq f (sp1, sp2)
       | (COE (tag1, sp1), COE (tag2, sp2)) =>
           tag1 = tag2 andalso spanEq f (sp1, sp2)
       | (CUST (opid1, ps1, _), CUST (opid2, ps2, _)) =>
           f (opid1, opid2) andalso paramsEq f (ps1, ps2)
       | (HYP_REF a, HYP_REF b) =>
           f (a, b)
       | (RULE_HYP a, RULE_HYP b) =>
           f (a, b)
       | (RULE_ELIM a, RULE_ELIM b) =>
           f (a, b)
       | (DEV_BOOL_ELIM a, DEV_BOOL_ELIM b) =>
           f (a, b)
       | (DEV_S1_ELIM a, DEV_S1_ELIM b) =>
           f (a, b)
       | (DEV_DFUN_ELIM a, DEV_DFUN_ELIM b) =>
           f (a, b)
       | _ => false
  end

  fun eq f =
    fn (MONO th1, MONO th2) => th1 = th2
     | (POLY th1, POLY th2) => eqPoly f (th1, th2)
     | _ => false

  val toStringMono =
    fn DFUN => "dfun"
     | LAM => "lam"
     | AP => "ap"
     | DPROD => "dprod"
     | PAIR => "pair"
     | FST => "fst"
     | SND => "snd"
     | BOOL => "bool"
     | TRUE => "tt"
     | FALSE => "ff"
     | IF => "if"
     | S1 => "S1"
     | BASE => "base"
     | S1_ELIM => "s1-elim"
     | AX => "ax"
     | ID_TY => "paths"
     | ID_ABS => "abs"
     | REFINE _ => "refine"
     | EXTRACT _ => "extract"
     | TAC_SEQ _ => "seq"
     | TAC_ORELSE => "orelse"
     | TAC_REC => "rec"
     | TAC_PROGRESS => "progress"
     | RULE_ID => "id"
     | RULE_AUTO => "auto-step"
     | RULE_AUTO_STEP => "auto"
     | RULE_SYMMETRY => "symmetry"
     | RULE_WITNESS => "witness"
     | RULE_HEAD_EXP => "head-expand"
     | RULE_CUT => "cut"
     | RULE_LEMMA _ => "lemma"
     | RULE_EVAL_GOAL => "eval-goal"
     | RULE_CEQUIV_REFL => "ceq/refl"
     | DEV_PATH_INTRO => "path-intro"
     | DEV_FUN_INTRO => "fun-intro"
     | DEV_DPROD_INTRO => "dprod-intro"
     | DEV_LET => "let"
     | MTAC_ALL => "all"
     | MTAC_EACH n => "each"
     | MTAC_FOCUS i => "focus{" ^ Int.toString i ^ "}"
     | JDG_EQ => "eq"
     | JDG_CEQ => "ceq"
     | JDG_MEM => "mem"
     | JDG_TRUE => "true"
     | JDG_EQ_TYPE => "eq-type"
     | JDG_TYPE => "type"
     | JDG_SYNTH => "synth"

  local
    fun spanToString f (r, r') =
      P.toString f r ^ " ~> " ^ P.toString f r'

    fun extentsToString f =
      ListSpine.pretty (P.toString f) ","

    fun paramsToString f =
      ListSpine.pretty (fn (p, _) => P.toString f p) ","

    val tagToString =
      fn TAG_NONE => ""
       | TAG_BOOL => "/bool"
       | TAG_S1 => "/S1"
       | TAG_DFUN => "/dfun"
       | TAG_DPROD => "/dprod"
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
       | CUST (opid, ps, ar) =>
           f opid ^ "{" ^ paramsToString f ps ^ "}"
       | UNIV lvl => "univ{" ^ P.toString f lvl ^ "}"
       | ID_AP r => "idap{" ^ P.toString f r ^ "}"
       | HYP_REF a => "@" ^ f a
       | RULE_HYP a => "hyp{" ^ f a ^ "}"
       | RULE_ELIM a => "elim{" ^ f a ^ "}"
       | DEV_BOOL_ELIM a => "bool-elim{" ^ f a ^ "}"
       | DEV_S1_ELIM a => "s1-elim{" ^ f a ^ "}"
       | DEV_DFUN_ELIM a => "dfun-elim{" ^ f a ^ "}"
  end

  fun toString f =
    fn MONO th => toStringMono th
     | POLY th => toStringPoly f th

  local
    fun mapSpan f (r, r') = (P.bind f r, P.bind f r')
    fun mapExtents f = List.map (P.bind f)
    fun mapParams (f : 'a -> 'b P.term) =
      List.map
        (fn (p, ann) =>
           let
             val q = P.bind f p
             val _ = Option.map (fn tau => P.check tau q) ann
           in
             (q, ann)
           end)

    fun mapSym f a =
      case f a of
         P.VAR a' => a'
       | _ => raise Fail "Expected symbol, but got application"

    fun mapLvl f a =
      let
        val r = f a
        val _ = P.check LVL r
      in
        r
      end
  in
    fun mapPoly f =
      fn LOOP r => LOOP (P.bind f r)
       | HCOM (tag, extents, dir) => HCOM (tag, mapExtents f extents, mapSpan f dir)
       | COE (tag, dir) => COE (tag, mapSpan f dir)
       | CUST (opid, ps, ar) => CUST (mapSym f opid, mapParams f ps, ar)
       | UNIV lvl => UNIV (P.bind (mapLvl f) lvl)
       | ID_AP r => ID_AP (P.bind f r)
       | HYP_REF a => HYP_REF (mapSym f a)
       | RULE_HYP a => RULE_HYP (mapSym f a)
       | RULE_ELIM a => RULE_ELIM (mapSym f a)
       | DEV_BOOL_ELIM a => DEV_BOOL_ELIM (mapSym f a)
       | DEV_S1_ELIM a => DEV_S1_ELIM (mapSym f a)
       | DEV_DFUN_ELIM a => DEV_DFUN_ELIM (mapSym f a)
  end

  fun map f =
    fn MONO th => MONO th
     | POLY th => POLY (mapPoly f th)

end
