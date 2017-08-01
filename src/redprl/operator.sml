structure RedPrlSortData =
struct
  datatype param_sort =
     DIM
   | HYP of sort
   | OPID

  and sort =
     EXP
   | TAC
   | MTAC
   | JDG
   | TRIV
   | PARAM_EXP of param_sort

  val rec sortToString = 
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | JDG => "jdg"
     | TRIV => "triv"
     | PARAM_EXP sigma => "param-exp{" ^ paramSortToString sigma ^ "}"

  and paramSortToString = 
    fn DIM => "dim"
     | HYP tau => "hyp{" ^ sortToString tau ^ "}"
     | OPID => "opid"
end

structure RedPrlParamData =
struct
  datatype 'a param_operator =
     DIM0
   | DIM1
end


structure RedPrlSort : ABT_SORT =
struct
  open RedPrlSortData

  type t = sort
  val eq : t * t -> bool = op=

  val toString = sortToString
end


structure RedPrlParamSort : ABT_SORT =
struct
  open RedPrlSortData RedPrlParamData

  type t = param_sort
  val eq : t * t -> bool = op=

  val toString = paramSortToString
end

structure RedPrlParameter : ABT_PARAMETER =
struct
  open RedPrlSortData RedPrlParamData
  type 'a t = 'a param_operator

  fun map _ =
    fn DIM0 => DIM0
     | DIM1 => DIM1

  structure Sort = RedPrlParamSort

  val arity =
    fn DIM0 => (DIM0, DIM)
     | DIM1 => (DIM1, DIM)

  fun eq _ =
    fn (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString _ =
    fn DIM0 => "0"
     | DIM1 => "1"

  fun join zer _ =
    fn DIM0 => zer
     | DIM1 => zer
end

structure RedPrlParameterTerm = AbtParameterTerm (RedPrlParameter)


structure RedPrlArity = ListAbtArity (structure PS = RedPrlParamSort and S = RedPrlSort)

structure RedPrlOpData =
struct
  open RedPrlSortData
  structure P = RedPrlParameterTerm
  type psort = RedPrlSortData.param_sort

  datatype 'a dev_pattern = 
     PAT_VAR of 'a
   | PAT_TUPLE of (string * 'a dev_pattern) list


  (* We split our operator signature into a couple datatypes, because the implementation of
   * some of the 2nd-order signature obligations can be made trivial for "constant" operators,
   * which we call "monomorphic".
   *
   * Practically, the difference is:
   * MONO: the Standard ML built-in equality properly compares the operators.
   * POLY: we have to compare the operators manually. *)
  datatype mono_operator =
   (* the trivial realizer of sort TRIV for judgments lacking interesting
    * computational content. *)
     TV
   (* the trivial realizer of sort EXP for types lacking interesting
    * computational content. This is the "ax(iom)" in Nuprl. *)
   | AX
   (* strict bool *)
   | BOOL | TT | FF | IF
   (* week bool *)
   | WBOOL | WIF
   (* natural numbers *)
   | NAT | ZERO | SUCC | NAT_REC
   (* integers *)
   | INT | NEGSUCC | INT_REC
   (* empty type *)
   | VOID
   (* circle *)
   | S1 | BASE | S1_REC
   (* function: lambda and app *)
   | DFUN | LAM | APP
   (* record and tuple *)
   | RECORD of string list | TUPLE of string list | PROJ of string | TUPLE_UPDATE of string
   (* path: path abstraction *)
   | PATH_TY | PATH_ABS

   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ of psort list | MTAC_ORELSE | MTAC_REC
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH of int | MTAC_FOCUS of int
   | MTAC_HOLE of string option
   | TAC_MTAC

   (* primitive rules *)
   | RULE_ID | RULE_AUTO_STEP | RULE_SYMMETRY | RULE_EXACT of RedPrlSort.t | RULE_HEAD_EXP
   | RULE_CUT
   | RULE_PRIM of string

   (* development calculus terms *)
   | DEV_DFUN_INTRO of unit dev_pattern list
   | DEV_PATH_INTRO of int | DEV_RECORD_INTRO of string list
   | DEV_LET of RedPrlSort.t

   | JDG_EQ | JDG_TRUE | JDG_EQ_TYPE | JDG_SYNTH | JDG_TERM of RedPrlSort.t | JDG_PARAM_SUBST of RedPrlParamSort.t list * RedPrlSort.t

  type psort = RedPrlArity.Vl.PS.t
  type 'a equation = 'a P.term * 'a P.term
  type 'a dir = 'a P.term * 'a P.term

  datatype 'a poly_operator =
     FCOM of 'a dir * 'a equation list
   | LOOP of 'a P.term
   | PATH_APP of 'a P.term
   | HCOM of 'a dir * 'a equation list
   | COE of 'a dir
   | COM of 'a dir * 'a equation list
   | CUST of 'a * ('a P.term * psort option) list * RedPrlArity.t option
   | RULE_CUT_LEMMA of 'a * ('a P.term * psort option) list
   | HYP_REF of 'a
   | PARAM_REF of psort * 'a P.term
   | RULE_HYP of 'a * sort
   | RULE_ELIM of 'a * sort
   | RULE_UNFOLD of 'a
   | DEV_BOOL_ELIM of 'a
   | DEV_S1_ELIM of 'a

   | DEV_APPLY_HYP of 'a * unit dev_pattern * int

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

  val rec devPatternSymValence = 
    fn PAT_VAR _ => [HYP EXP]
     | PAT_TUPLE pats => List.concat (List.map (devPatternSymValence o #2) pats)

  val arityMono =
    fn TV => [] ->> TRIV
     | AX => [] ->> EXP

     | BOOL => [] ->> EXP
     | TT => [] ->> EXP
     | FF => [] ->> EXP
     | IF => [[] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP

     | WBOOL => [] ->> EXP
     | WIF => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP

     | VOID => [] ->> EXP

     | NAT => [] ->> EXP
     | ZERO => [] ->> EXP
     | SUCC => [[] * [] <> EXP] ->> EXP
     | NAT_REC => [[] * [] <> EXP, [] * [] <> EXP, [] * [EXP, EXP] <> EXP] ->> EXP
     | INT => [] ->> EXP
     | NEGSUCC => [[] * [] <> EXP] ->> EXP
     | INT_REC => [[] * [] <> EXP, [] * [EXP, EXP] <> EXP, [] * [] <> EXP, [] * [EXP, EXP] <> EXP] ->> EXP

     | S1 => [] ->> EXP
     | BASE => [] ->> EXP
     | S1_REC => [[] * [EXP] <> EXP, [] * [] <> EXP, [] * [] <> EXP, [DIM] * [] <> EXP] ->> EXP

     | DFUN => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
     | LAM => [[] * [EXP] <> EXP] ->> EXP
     | APP => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP

     | RECORD lbls =>
       let
         val (_, valences) = List.foldr (fn (_, (taus, vls)) => (EXP :: taus, ([] * taus <> EXP) :: vls)) ([], []) lbls
       in 
         List.rev valences ->> EXP
       end
     | TUPLE lbls => (map (fn _ => ([] * [] <> EXP)) lbls) ->> EXP
     | PROJ lbl => [[] * [] <> EXP] ->> EXP
     | TUPLE_UPDATE lbl => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP

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
     | MTAC_FOCUS _ => [[] * [] <> TAC] ->> MTAC
     | MTAC_HOLE _ => [] ->> MTAC
     | TAC_MTAC => [[] * [] <> MTAC] ->> TAC

     | RULE_ID => [] ->> TAC
     | RULE_AUTO_STEP => [] ->> TAC
     | RULE_SYMMETRY => [] ->> TAC
     | RULE_EXACT tau => [[] * [] <> tau] ->> TAC
     | RULE_HEAD_EXP => [] ->> TAC
     | RULE_CUT => [[] * [] <> JDG] ->> TAC
     | RULE_PRIM _ => [] ->> TAC

     | DEV_DFUN_INTRO pats => [List.concat (List.map devPatternSymValence pats) * [] <> TAC] ->> TAC
     | DEV_RECORD_INTRO lbls => List.map (fn _ => [] * [] <> TAC) lbls ->> TAC
     | DEV_PATH_INTRO n => [List.tabulate (n, fn _ => DIM) * [] <> TAC] ->> TAC
     | DEV_LET tau => [[] * [] <> JDG, [] * [] <> TAC, [HYP tau] * [] <> TAC] ->> TAC

     | JDG_EQ => [[] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> JDG
     | JDG_TRUE => [[] * [] <> EXP] ->> JDG
     | JDG_EQ_TYPE => [[] * [] <> EXP, [] * [] <> EXP] ->> JDG
     | JDG_SYNTH => [[] * [] <> EXP] ->> JDG
     | JDG_TERM _ => [] ->> JDG
     | JDG_PARAM_SUBST (sigmas, tau) => List.map (fn sigma => [] * [] <> PARAM_EXP sigma) sigmas @ [sigmas * [] <> tau] ->> JDG

  local
    fun arityFcom (_, eqs) =
      let
        val capArg = [] * [] <> EXP
        val tubeArgs = List.map (fn _ => [DIM] * [] <> EXP) eqs
      in
        capArg :: tubeArgs ->> EXP
      end
    fun arityHcom (_, eqs) =
      let
        val typeArg = [] * [] <> EXP
        val capArg = [] * [] <> EXP
        val tubeArgs = List.map (fn _ => [DIM] * [] <> EXP) eqs
      in
        typeArg :: capArg :: tubeArgs ->> EXP
      end
    fun arityCom (_, eqs) =
      let
        val typeArg = [DIM] * [] <> EXP
        val capArg = [] * [] <> EXP
        val tubeArgs = List.map (fn _ => [DIM] * [] <> EXP) eqs
      in
        typeArg :: capArg :: tubeArgs ->> EXP
      end
  in
    val arityPoly =
      fn FCOM params => arityFcom params
       | LOOP _ => [] ->> EXP
       | PATH_APP _ => [[] * [] <> EXP] ->> EXP
       | HCOM params => arityHcom params
       | COE _ => [[DIM] * [] <> EXP, [] * [] <> EXP] ->> EXP
       | COM params => arityCom params
       | CUST (_, _, ar) => Option.valOf ar
       | RULE_CUT_LEMMA (_, _) => [] ->> TAC
       | HYP_REF _ => [] ->> EXP
       | PARAM_REF (sigma, _) => [] ->> PARAM_EXP sigma
       | RULE_HYP _ => [] ->> TAC
       | RULE_ELIM _ => [] ->> TAC
       | RULE_UNFOLD _ => [] ->> TAC
       | DEV_BOOL_ELIM _ => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
       | DEV_S1_ELIM _ => [[] * [] <> TAC, [DIM] * [] <> TAC] ->> TAC
       | DEV_APPLY_HYP (_, pat, n) => List.tabulate (n, fn _ => [] * [] <> TAC) @ [devPatternSymValence pat * [] <> TAC] ->> TAC
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

    fun spansSupport ss =
      ListMonad.bind spanSupport ss

    fun comSupport (dir, eqs) =
      spanSupport dir @ spansSupport eqs

    fun paramsSupport ps =
      ListMonad.bind
        (fn (P.VAR a, SOME tau) => [(a, tau)]
          | (P.VAR _, NONE) => raise Fail "Encountered unannotated parameter in custom operator"
          | (P.APP t, _) => P.freeVars t)
        ps

  in
    val supportPoly =
      fn FCOM params => comSupport params
       | LOOP r => dimSupport r
       | PATH_APP r => dimSupport r
       | HCOM params => comSupport params
       | COE dir => spanSupport dir
       | COM params => comSupport params
       | CUST (opid, ps, _) => (opid, OPID) :: paramsSupport ps
       | RULE_CUT_LEMMA (opid, ps) => (opid, OPID) :: paramsSupport ps
       | HYP_REF a => [(a, HYP EXP)]
       | PARAM_REF (sigma, r) => paramsSupport [(r, SOME sigma)]
       | RULE_HYP (a, tau) => [(a, HYP tau)]
       | RULE_ELIM (a, tau) => [(a, HYP tau)]
       | RULE_UNFOLD a => [(a, OPID)]
       | DEV_BOOL_ELIM a => [(a, HYP EXP)]
       | DEV_S1_ELIM a => [(a, HYP EXP)]
       | DEV_APPLY_HYP (a, _, _) => [(a, HYP EXP)]
  end

  val support =
    fn MONO _ => []
     | POLY th => supportPoly th

  local
    fun spanEq f ((r1, r'1), (r2, r'2)) =
      P.eq f (r1, r2) andalso P.eq f (r'1, r'2)

    fun spansEq f =
      ListPair.allEq (spanEq f)

    fun paramsEq f =
      ListPair.allEq (fn ((p, _), (q, _)) => P.eq f (p, q))
  in
    fun eqPoly f =
      fn (FCOM (dir1, eqs1), t) =>
         (case t of
             FCOM (dir2, eqs2) => spanEq f (dir1, dir2) andalso spansEq f (eqs1, eqs2)
           | _ => false)
       | (LOOP r, t) => (case t of LOOP r' => P.eq f (r, r') | _ => false)
       | (PATH_APP r, t) => (case t of PATH_APP r' => P.eq f (r, r') | _ => false)
       | (HCOM (dir1, eqs1), t) =>
         (case t of
             HCOM (dir2, eqs2) => spanEq f (dir1, dir2) andalso spansEq f (eqs1, eqs2)
           | _ => false)
       | (COE dir1, t) =>
         (case t of
             COE dir2 => spanEq f (dir1, dir2)
            | _ => false)
       | (COM (dir1, eqs1), t) =>
         (case t of
             COM (dir2, eqs2) => spanEq f (dir1, dir2) andalso spansEq f (eqs1, eqs2)
            | _ => false)
       | (CUST (opid1, ps1, _), t) =>
         (case t of
             CUST (opid2, ps2, _) => f (opid1, opid2) andalso paramsEq f (ps1, ps2)
           | _ => false)
       | (RULE_CUT_LEMMA (opid1, ps1), t) =>
         (case t of
             RULE_CUT_LEMMA (opid2, ps2) => f (opid1, opid2) andalso paramsEq f (ps1, ps2)
           | _ => false)
       | (HYP_REF a, t) => (case t of HYP_REF b => f (a, b) | _ => false)
       | (PARAM_REF (sigma1, r1), t) => (case t of PARAM_REF (sigma2, r2) => sigma1 = sigma2 andalso P.eq f (r1, r2) | _ => false)
       | (RULE_HYP (a, _), t) => (case t of RULE_HYP (b, _) => f (a, b) | _ => false)
       | (RULE_ELIM (a, _), t) => (case t of RULE_ELIM (b, _) => f (a, b) | _ => false)
       | (RULE_UNFOLD a, t) => (case t of RULE_UNFOLD b => f (a, b) | _ => false)
       | (DEV_BOOL_ELIM a, t) => (case t of DEV_BOOL_ELIM b => f (a, b) | _ => false)
       | (DEV_S1_ELIM a, t) => (case t of DEV_S1_ELIM b => f (a, b) | _ => false)
       | (DEV_APPLY_HYP (a, pat, n), t) => (case t of DEV_APPLY_HYP (b, pat', n') => f (a, b) andalso pat = pat' andalso n = n' | _ => false)
  end

  fun eq f =
    fn (MONO th1, MONO th2) => th1 = th2
     | (POLY th1, POLY th2) => eqPoly f (th1, th2)
     | _ => false

  val toStringMono =
    fn TV => "tv"
     | AX => "ax"

     | WBOOL => "wbool"
     | WIF => "wif"

     | BOOL => "bool"
     | TT => "tt"
     | FF => "ff"
     | IF => "if"

     | NAT => "nat"
     | NAT_REC => "nat-rec"
     | ZERO => "zero"
     | SUCC => "succ"
     | INT => "int"
     | NEGSUCC => "negsucc"
     | INT_REC => "int-rec"

     | VOID => "void"

     | S1 => "S1"
     | BASE => "base"
     | S1_REC => "S1-rec"

     | DFUN => "dfun"
     | LAM => "lam"
     | APP => "app"

     | RECORD lbls => "record{" ^ ListSpine.pretty (fn s => s) "," lbls ^ "}"
     | TUPLE lbls => "tuple{" ^ ListSpine.pretty (fn s => s) "," lbls ^ "}"
     | PROJ lbl => "proj{" ^ lbl ^ "}"
     | TUPLE_UPDATE lbl => "update{" ^ lbl ^ "}"

     | PATH_TY => "path"
     | PATH_ABS => "abs"

     | MTAC_SEQ psorts => "seq{" ^ ListSpine.pretty RedPrlParamSort.toString "," psorts ^ "}"
     | MTAC_ORELSE => "orelse"
     | MTAC_REC => "rec"
     | MTAC_REPEAT => "repeat"
     | MTAC_AUTO => "auto"
     | MTAC_PROGRESS => "multi-progress"
     | MTAC_ALL => "all"
     | MTAC_EACH _ => "each"
     | MTAC_FOCUS i => "focus{" ^ Int.toString i ^ "}"
     | MTAC_HOLE (SOME x) => "?" ^ x
     | MTAC_HOLE NONE => "?"
     | TAC_MTAC => "mtac"

     | RULE_ID => "id"
     | RULE_AUTO_STEP => "auto-step"
     | RULE_SYMMETRY => "symmetry"
     | RULE_EXACT _ => "exact"
     | RULE_HEAD_EXP => "head-expand"
     | RULE_CUT => "cut"
     | RULE_PRIM name => "refine{" ^ name ^ "}"

     | DEV_PATH_INTRO n => "path-intro{" ^ Int.toString n ^ "}"
     | DEV_DFUN_INTRO pats => "fun-intro"
     | DEV_RECORD_INTRO lbls => "record-intro{" ^ ListSpine.pretty (fn x => x) "," lbls ^ "}"
     | DEV_LET _ => "let"

     | JDG_EQ => "eq"
     | JDG_TRUE => "true"
     | JDG_EQ_TYPE => "eq-type"
     | JDG_SYNTH => "synth"
     | JDG_TERM tau => RedPrlSort.toString tau
     | JDG_DIM_SUBST => "dim-subst"

  local
    fun dirToString f (r, r') =
      P.toString f r ^ " ~> " ^ P.toString f r'

    fun equationToString f (r, r') =
      P.toString f r ^ "=" ^ P.toString f r'

    fun equationsToString f =
      ListSpine.pretty (equationToString f) ","

    fun paramsToString f =
      ListSpine.pretty (fn (p, _) => P.toString f p) ","
  in
    fun toStringPoly f =
      fn FCOM (dir, eqs) =>
           "fcom"
             ^ "["
             ^ equationsToString f eqs
             ^ "; "
             ^ dirToString f dir
             ^ "]"
       | LOOP r => "loop[" ^ P.toString f r ^ "]"
       | PATH_APP r => "pathapp{" ^ P.toString f r ^ "}"
       | HCOM (dir, eqs) =>
           "hcom"
             ^ "["
             ^ equationsToString f eqs
             ^ "; "
             ^ dirToString f dir
             ^ "]"
       | COE dir =>
           "coe"
             ^ "["
             ^ dirToString f dir
             ^ "]"
       | COM (dir, eqs) =>
           "com"
             ^ "["
             ^ equationsToString f eqs
             ^ "; "
             ^ dirToString f dir
             ^ "]"
       | CUST (opid, [], _) =>
           f opid
       | CUST (opid, ps, _) =>
           f opid ^ "{" ^ paramsToString f ps ^ "}"
       | RULE_CUT_LEMMA (opid, ps) =>
           "cut-lemma{" ^ f opid ^ "}{" ^ paramsToString f ps ^ "}"
       | HYP_REF a => "hyp-ref{" ^ f a ^ "}"
       | PARAM_REF (_, r) => "param-ref{" ^ P.toString f r ^ "}"
       | RULE_HYP (a, _) => "hyp{" ^ f a ^ "}"
       | RULE_ELIM (a, _) => "elim{" ^ f a ^ "}"
       | RULE_UNFOLD a => "unfold{" ^ f a ^ "}"
       | DEV_BOOL_ELIM a => "bool-elim{" ^ f a ^ "}"
       | DEV_S1_ELIM a => "s1-elim{" ^ f a ^ "}"
       | DEV_APPLY_HYP (a, _, _) => "apply-hyp{" ^ f a ^ "}"
  end

  fun toString f =
    fn MONO th => toStringMono th
     | POLY th => toStringPoly f th

  local
    fun passSort sigma f = 
      fn u => f (u, sigma)

    fun mapSpan f (r, r') = (P.bind (passSort DIM f) r, P.bind (passSort DIM f) r')
    fun mapSpans f = List.map (mapSpan f)
    fun mapParams (f : 'a * psort -> 'b P.term) =
      List.map
        (fn (p, SOME tau) =>
           let
             val q = P.bind (passSort tau f) p
             val _ = P.check tau q
           in
             (q, SOME tau)
           end
          | _ => raise Fail "operator.sml, uh-oh")

    fun mapSym f a =
      case f a of
         P.VAR a' => a'
       | P.APP _ => raise Fail "Expected symbol, but got application"
  in
    fun mapPolyWithSort f =
      fn FCOM (dir, eqs) => FCOM (mapSpan f dir, mapSpans f eqs)
       | LOOP r => LOOP (P.bind (passSort DIM f) r)
       | PATH_APP r => PATH_APP (P.bind (passSort DIM f) r)
       | HCOM (dir, eqs) => HCOM (mapSpan f dir, mapSpans f eqs)
       | COE dir => COE (mapSpan f dir)
       | COM (dir, eqs) => COM (mapSpan f dir, mapSpans f eqs)
       | CUST (opid, ps, ar) => CUST (mapSym (passSort OPID f) opid, mapParams f ps, ar)
       | RULE_CUT_LEMMA (opid, ps) => RULE_CUT_LEMMA (mapSym (passSort OPID f) opid, mapParams f ps)
       | HYP_REF a => HYP_REF (mapSym (passSort (HYP EXP) f) a)
       | PARAM_REF (sigma, r) => PARAM_REF (sigma, P.bind (passSort sigma f) r)
       | RULE_HYP (a, tau) => RULE_HYP (mapSym (passSort (HYP tau) f) a, tau)
       | RULE_ELIM (a, tau) => RULE_ELIM (mapSym (passSort (HYP tau) f) a, tau)
       | RULE_UNFOLD a => RULE_UNFOLD (mapSym (passSort OPID f) a)
       | DEV_BOOL_ELIM a => DEV_BOOL_ELIM (mapSym (passSort (HYP EXP) f) a)
       | DEV_S1_ELIM a => DEV_S1_ELIM (mapSym (passSort (HYP EXP) f) a)
       | DEV_APPLY_HYP (a, pat, spine) => DEV_APPLY_HYP (mapSym (passSort (HYP EXP) f) a, pat, spine)
  end

  fun mapWithSort f =
    fn MONO th => MONO th
     | POLY th => POLY (mapPolyWithSort f th)

  fun map f = 
    mapWithSort (fn (u, _) => f u)
end
