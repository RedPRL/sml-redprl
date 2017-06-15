structure RedPrlSortData =
struct
  datatype sort =
     EXP
   | TAC
   | MTAC
   | JDG
   | TRIV

  datatype param_sort =
     DIM
   | EXN
   | LBL
   | OPID
   | HYP of sort
end

structure RedPrlParamData =
struct
  datatype 'a param_operator =
     DIM0
   | DIM1

  val invert =
    fn DIM0 => DIM1
     | DIM1 => DIM0
end

structure RedPrlParamSort : ABT_SORT =
struct
  open RedPrlSortData RedPrlParamData

  type t = param_sort
  val eq : t * t -> bool = op=

  val toString =
    fn DIM => "dim"
     | EXN => "exn"
     | LBL => "lbl"
     | OPID => "opid"
     | HYP _ => "hyp"
end

structure RedPrlParameter : ABT_PARAMETER =
struct
  open RedPrlSortData RedPrlParamData
  type 'a t = 'a param_operator

  fun map f =
    fn DIM0 => DIM0
     | DIM1 => DIM1

  structure Sort = RedPrlParamSort

  val arity =
    fn DIM0 => (DIM0, DIM)
     | DIM1 => (DIM1, DIM)

  fun eq f =
    fn (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn DIM0 => "0"
     | DIM1 => "1"

  fun join zer mul =
    fn DIM0 => zer
     | DIM1 => zer
end

structure RedPrlParameterTerm = AbtParameterTerm (RedPrlParameter)


structure RedPrlSort : ABT_SORT =
struct
  open RedPrlSortData

  type t = sort
  val eq : t * t -> bool = op=

  val rec toString =
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | JDG => "jdg"
     | TRIV => "triv"
end

structure RedPrlArity = ListAbtArity (structure PS = RedPrlParamSort and S = RedPrlSort)

structure RedPrlOpData =
struct
  open RedPrlSortData
  structure P = RedPrlParameterTerm
  type psort = RedPrlSortData.param_sort

  (* We split our operator signature into a couple datatypes, because the implementation of
   * some of the 2nd-order signature obligations can be made trivial for "constant" operators,
   * which we call "monomorphic".
   *
   * Practically, the difference is:
   * MONO: the Standard ML built-in equality properly compares the operators.
   * POLY: we have to compare the operators manually. *)
  datatype mono_operator =
   (* axioms *)
     AX
   (* week bool: true, false and if *)
   | BOOL | TRUE | FALSE | IF (* weak booleans *)
   (* strict bool: strict if (true and false are shared) *)
   | S_BOOL | S_IF
   (* circle: base and s1_elim *)
   | S1 | BASE | S1_ELIM
   (* function: lambda and app *)
   | DFUN | LAM | AP
   (* prodcut: pair, fst and snd *)
   | DPROD | PAIR | FST | SND
   (* path: path abstraction *)
   | PATH_TY | PATH_ABS

   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ of psort list | MTAC_ORELSE | MTAC_REC
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH of int | MTAC_FOCUS of int
   | MTAC_HOLE of string option
   | TAC_MTAC

   (* primitive rules *)
   | RULE_ID | RULE_EVAL_GOAL | RULE_CEQUIV_REFL | RULE_AUTO_STEP | RULE_SYMMETRY | RULE_WITNESS | RULE_HEAD_EXP
   | RULE_CUT

   (* development calculus terms *)
   | DEV_DFUN_INTRO | DEV_DPROD_INTRO | DEV_PATH_INTRO
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
   | TAG_PATH

  type psort = RedPrlArity.Vl.PS.t
  type 'a equation = 'a P.term * 'a P.term
  type 'a equations = 'a equation list
  type 'a dir = 'a P.term * 'a P.term

  datatype 'a poly_operator =
     LOOP of 'a P.term
   | PATH_AP of 'a P.term
   | HCOM of type_tag * 'a equations * 'a dir
   | COE of type_tag * 'a dir
   | CUST of 'a * ('a P.term * psort option) list * RedPrlArity.t option
   | RULE_LEMMA of 'a * ('a P.term * psort option) list * RedPrlArity.t option
   | HYP_REF of 'a
   | RULE_HYP of 'a * sort
   | RULE_ELIM of 'a * sort
   | RULE_UNFOLD of 'a
   | DEV_BOOL_ELIM of 'a
   | DEV_S1_ELIM of 'a
   | DEV_DFUN_ELIM of 'a
   | DEV_DPROD_ELIM of 'a

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
    fn AX => [] ->> TRIV

     | BOOL => [] ->> EXP
     | TRUE => [] ->> EXP
     | FALSE => [] ->> EXP
     | IF => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP

     | S_BOOL => [] ->> EXP
     | S_IF => [[] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP

     | S1 => [] ->> EXP
     | BASE => [] ->> EXP
     | S1_ELIM => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP, [DIM] * [] <> EXP] ->> EXP

     | DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
     | LAM => [[] * [EXP] <> EXP] ->> EXP
     | AP => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP

     | DPROD => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
     | PAIR => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | FST => [[] * [] <> EXP] ->> EXP
     | SND => [[] * [] <> EXP] ->> EXP

     | PATH_TY => [[DIM] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP
     | PATH_ABS => [[DIM] * [] <> EXP] ->> EXP

     | MTAC_SEQ psorts => [[] * [] <> MTAC, psorts * [] <> MTAC] ->> MTAC
     | MTAC_ORELSE => [[] * [] <> MTAC, [] * [] <> MTAC] ->> MTAC
     | MTAC_REC => [[] * [MTAC] <> MTAC] ->> MTAC
     | MTAC_REPEAT => [[] * [] <> MTAC] ->> MTAC
     | MTAC_AUTO => [] ->> MTAC
     | MTAC_PROGRESS => [[] * [] <> MTAC] ->> MTAC
     | MTAC_ALL => [[] * [] <> TAC] ->> MTAC
     | MTAC_EACH n =>
         let
           val tacs = List.tabulate (n, fn _ => [] * [] <> TAC)
         in
           tacs ->> MTAC
         end
     | MTAC_FOCUS i => [[] * [] <> TAC] ->> MTAC
     | MTAC_HOLE _ => [] ->> MTAC
     | TAC_MTAC => [[] * [] <> MTAC] ->> TAC

     | RULE_ID => [] ->> TAC
     | RULE_EVAL_GOAL => [] ->> TAC
     | RULE_CEQUIV_REFL => [] ->> TAC
     | RULE_AUTO_STEP => [] ->> TAC
     | RULE_SYMMETRY => [] ->> TAC
     | RULE_WITNESS => [[] * [] <> EXP] ->> TAC
     | RULE_HEAD_EXP => [] ->> TAC
     | RULE_CUT => [[] * [] <> JDG] ->> TAC

     | DEV_DFUN_INTRO => [[HYP EXP] * [] <> TAC] ->> TAC
     | DEV_DPROD_INTRO => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
     | DEV_PATH_INTRO => [[DIM] * [] <> TAC] ->> TAC
     | DEV_LET => [[] * [] <> JDG, [] * [] <> TAC, [HYP EXP] * [] <> TAC] ->> TAC

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
       | TAG_PATH => [[DIM] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP]

    fun arityHcom (tag, equations, dir) =
      let
        val typeArgs = typeArgsForTag tag
        val capArg = [] * [] <> EXP
        val tubeArgs =
          List.map
            (fn _ => [DIM] * [] <> EXP)
            equations
      in
        typeArgs @ capArg :: tubeArgs ->> EXP
      end

    fun arityCoe (tag, dir) =
      let
        val typeArgs =
          List.map
            (fn ((sigmas, taus),tau) => (DIM :: sigmas) * taus <> tau)
            (typeArgsForTag tag)
      in
        typeArgs @ [[] * [] <> EXP] ->> EXP
      end
  in
    val arityPoly =
      fn LOOP _ => [] ->> EXP
       | PATH_AP r => [[] * [] <> EXP] ->> EXP
       | HCOM hcom => arityHcom hcom
       | COE coe => arityCoe coe
       | CUST (_, _, ar) => Option.valOf ar
       | RULE_LEMMA (_, _, ar) => (#1 (Option.valOf ar), TAC)
       | HYP_REF a => [] ->> EXP
       | RULE_HYP _ => [] ->> TAC
       | RULE_ELIM _ => [] ->> TAC
       | RULE_UNFOLD a => [] ->> TAC
       | DEV_BOOL_ELIM a => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
       | DEV_S1_ELIM a => [[] * [] <> TAC, [DIM] * [] <> TAC] ->> TAC
       | DEV_DFUN_ELIM a => [[] * [] <> TAC, [HYP EXP, HYP EXP] * [] <> TAC] ->> TAC
       | DEV_DPROD_ELIM a => [[HYP EXP, HYP EXP] * [] <> TAC] ->> TAC
  end

  val arity =
    fn MONO th => arityMono th
     | POLY th => arityPoly th

  local
    val dimSupport =
      fn P.VAR a => [(a, DIM)]
       | P.APP t => P.freeVars t

    fun equationSupport (r, r') =
      dimSupport r @ dimSupport r'

    fun spanSupport (r, r') =
      dimSupport r @ dimSupport r'

    fun paramsSupport ps =
      ListMonad.bind
        (fn (P.VAR a, SOME tau) => [(a, tau)]
          | (P.VAR a, NONE) => raise Fail "Encountered unannotated parameter in custom operator"
          | (P.APP t, tau) => P.freeVars t)
        ps

  in
    val supportPoly =
      fn LOOP r => dimSupport r
       | PATH_AP r => dimSupport r
       | HCOM (_, equations, dir) =>
           ListMonad.bind equationSupport equations
             @ spanSupport dir
       | COE (_, dir) => spanSupport dir
       | CUST (opid, ps, _) => (opid, OPID) :: paramsSupport ps
       | RULE_LEMMA (opid, ps, _) => (opid, OPID) :: paramsSupport ps
       | HYP_REF a => [(a, HYP EXP)]
       | RULE_HYP (a, tau) => [(a, HYP tau)]
       | RULE_ELIM (a, tau) => [(a, HYP tau)]
       | RULE_UNFOLD a => [(a, OPID)]
       | DEV_BOOL_ELIM a => [(a, HYP EXP)]
       | DEV_S1_ELIM a => [(a, HYP EXP)]
       | DEV_DFUN_ELIM a => [(a, HYP EXP)]
       | DEV_DPROD_ELIM a => [(a, HYP EXP)]
  end

  val support =
    fn MONO th => []
     | POLY th => supportPoly th

  local
    fun spanEq f ((r1, r'1), (r2, r'2)) =
      P.eq f (r1, r2) andalso P.eq f (r'1, r'2)

    fun equationsEq f =
      ListPair.allEq (fn ((r1, r'1), (r2, r'2)) =>
        P.eq f (r1, r2) andalso P.eq f (r'1, r'2))

    fun paramsEq f =
      ListPair.allEq (fn ((p, _), (q, _)) => P.eq f (p, q))
  in
    fun eqPoly f =
      fn (LOOP r, t) => (case t of LOOP r' => P.eq f (r, r') | _ => false)
       | (PATH_AP r, t) => (case t of PATH_AP r' => P.eq f (r, r') | _ => false)
       | (HCOM (tag1, exs1, sp1), t) =>
           (case t of
                 HCOM (tag2, exs2, sp2) =>
                   tag1 = tag2
                   andalso equationsEq f (exs1, exs2)
                   andalso spanEq f (sp1, sp2)
               | _ => false)
       | (COE (tag1, sp1), t) =>
           (case t of
                 COE (tag2, sp2) =>
                   tag1 = tag2 andalso spanEq f (sp1, sp2)
               | _ => false)
       | (CUST (opid1, ps1, _), t) =>
           (case t of
                 CUST (opid2, ps2, _) =>
                   f (opid1, opid2) andalso paramsEq f (ps1, ps2)
               | _ => false)
       | (RULE_LEMMA (opid1, ps1, _), t) =>
           (case t of
                 RULE_LEMMA (opid2, ps2, _) =>
                   f (opid1, opid2) andalso paramsEq f (ps1, ps2)
               | _ => false)
       | (HYP_REF a, t) =>
           (case t of HYP_REF b => f (a, b) | _ => false)
       | (RULE_HYP (a, _), t) =>
           (case t of RULE_HYP (b, _) => f (a, b) | _ => false)
       | (RULE_ELIM (a, _), t) =>
           (case t of RULE_ELIM (b, _) => f (a, b) | _ => false)
       | (RULE_UNFOLD a, t) =>
           (case t of RULE_UNFOLD b => f (a, b) | _ => false)
       | (DEV_BOOL_ELIM a, t) =>
           (case t of DEV_BOOL_ELIM b => f (a, b) | _ => false)
       | (DEV_S1_ELIM a, t) =>
           (case t of DEV_S1_ELIM b => f (a, b) | _ => false)
       | (DEV_DFUN_ELIM a, t) =>
           (case t of DEV_DFUN_ELIM b => f (a, b) | _ => false)
       | (DEV_DPROD_ELIM a, t) =>
           (case t of DEV_DPROD_ELIM b => f (a, b) | _ => false)
  end

  fun eq f =
    fn (MONO th1, MONO th2) => th1 = th2
     | (POLY th1, POLY th2) => eqPoly f (th1, th2)
     | _ => false

  val toStringMono =
    fn AX => "ax"

     | BOOL => "bool"
     | TRUE => "tt"
     | FALSE => "ff"
     | IF => "if"

     | S_BOOL => "sbool"
     | S_IF => "if"

     | S1 => "S1"
     | BASE => "base"
     | S1_ELIM => "s1-elim"

     | DFUN => "dfun"
     | LAM => "lam"
     | AP => "ap"

     | DPROD => "dprod"
     | PAIR => "pair"
     | FST => "fst"
     | SND => "snd"

     | PATH_TY => "paths"
     | PATH_ABS => "abs"

     | MTAC_SEQ _ => "seq"
     | MTAC_ORELSE => "orelse"
     | MTAC_REC => "rec"
     | MTAC_REPEAT => "repeat"
     | MTAC_AUTO => "auto"
     | MTAC_PROGRESS => "multi-progress"
     | MTAC_ALL => "all"
     | MTAC_EACH n => "each"
     | MTAC_FOCUS i => "focus{" ^ Int.toString i ^ "}"
     | MTAC_HOLE (SOME x) => "?" ^ x
     | MTAC_HOLE NONE => "?"
     | TAC_MTAC => "mtac"

     | RULE_ID => "id"
     | RULE_EVAL_GOAL => "eval-goal"
     | RULE_CEQUIV_REFL => "ceq/refl"
     | RULE_AUTO_STEP => "auto-step"
     | RULE_SYMMETRY => "symmetry"
     | RULE_WITNESS => "witness"
     | RULE_HEAD_EXP => "head-expand"
     | RULE_CUT => "cut"

     | DEV_PATH_INTRO => "path-intro"
     | DEV_DFUN_INTRO => "fun-intro"
     | DEV_DPROD_INTRO => "dprod-intro"
     | DEV_LET => "let"

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

    fun equationToString f (r, r') =
      P.toString f r ^ "=" ^ P.toString f r'

    fun equationsToString f =
      ListSpine.pretty (equationToString f) ","

    fun paramsToString f =
      ListSpine.pretty (fn (p, _) => P.toString f p) ","

    val tagToString =
      fn TAG_NONE => ""
       | TAG_BOOL => "/bool"
       | TAG_S1 => "/S1"
       | TAG_DFUN => "/dfun"
       | TAG_DPROD => "/dprod"
       | TAG_PATH => "/path"
  in
    fun toStringPoly f =
      fn LOOP r => "loop[" ^ P.toString f r ^ "]"
       | PATH_AP r => "pathap{" ^ P.toString f r ^ "}"
       | HCOM (tag, equations, dir) =>
           "hcom"
             ^ tagToString tag
             ^ "["
             ^ equationsToString f equations
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
       | RULE_LEMMA (opid, ps, ar) =>
           "lemma{" ^ f opid ^ "}{" ^ paramsToString f ps ^ "}"
       | HYP_REF a => "@" ^ f a
       | RULE_HYP (a, _) => "hyp{" ^ f a ^ "}"
       | RULE_ELIM (a, _) => "elim{" ^ f a ^ "}"
       | RULE_UNFOLD a => "unfold{" ^ f a ^ "}"
       | DEV_BOOL_ELIM a => "bool-elim{" ^ f a ^ "}"
       | DEV_S1_ELIM a => "s1-elim{" ^ f a ^ "}"
       | DEV_DFUN_ELIM a => "dfun-elim{" ^ f a ^ "}"
       | DEV_DPROD_ELIM a => "dprod-elim{" ^ f a ^ "}"
  end

  fun toString f =
    fn MONO th => toStringMono th
     | POLY th => toStringPoly f th

  local
    fun mapSpan f (r, r') = (P.bind f r, P.bind f r')
    fun mapEquations f = List.map (fn (r, r') => (P.bind f r , P.bind f r'))
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
       | P.APP _ => raise Fail "Expected symbol, but got application"
  in
    fun mapPoly f =
      fn LOOP r => LOOP (P.bind f r)
       | PATH_AP r => PATH_AP (P.bind f r)
       | HCOM (tag, equations, dir) => HCOM (tag, mapEquations f equations, mapSpan f dir)
       | COE (tag, dir) => COE (tag, mapSpan f dir)
       | CUST (opid, ps, ar) => CUST (mapSym f opid, mapParams f ps, ar)
       | RULE_LEMMA (opid, ps, ar) => RULE_LEMMA (mapSym f opid, mapParams f ps, ar)
       | HYP_REF a => HYP_REF (mapSym f a)
       | RULE_HYP (a, tau) => RULE_HYP (mapSym f a, tau)
       | RULE_ELIM (a, tau) => RULE_ELIM (mapSym f a, tau)
       | RULE_UNFOLD a => RULE_UNFOLD (mapSym f a)
       | DEV_BOOL_ELIM a => DEV_BOOL_ELIM (mapSym f a)
       | DEV_S1_ELIM a => DEV_S1_ELIM (mapSym f a)
       | DEV_DFUN_ELIM a => DEV_DFUN_ELIM (mapSym f a)
       | DEV_DPROD_ELIM a => DEV_DPROD_ELIM (mapSym f a)
  end

  fun map f =
    fn MONO th => MONO th
     | POLY th => POLY (mapPoly f th)

end
