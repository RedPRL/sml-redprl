structure RedPrlSortData =
struct
  datatype param_sort =
     DIM
   | HYP
   | LVL
   | META_NAME
   | OPID

  and sort =
     EXP
   | TAC
   | MTAC
   | JDG
   | TRIV
   | MATCH_CLAUSE of sort
   | PARAM_EXP of param_sort

  val rec sortToString = 
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | JDG => "jdg"
     | TRIV => "triv"
     | MATCH_CLAUSE tau => "match-clause"
     | PARAM_EXP sigma => "param-exp{" ^ paramSortToString sigma ^ "}"

  and paramSortToString = 
    fn DIM => "dim"
     | HYP => "hyp"
     | LVL => "lvl"
     | META_NAME => "meta-name"
     | OPID => "opid"
end

structure RedPrlParamData =
struct
  datatype 'a param_operator =
     DIM0
   | DIM1
   | LCONST of IntInf.int
   | LABOVE of 'a * IntInf.int
   | LMAX of 'a list
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

  fun map f =
    fn DIM0 => DIM0
     | DIM1 => DIM1
     | LCONST i => LCONST i
     | LABOVE (l, i) => LABOVE (f l, i)
     | LMAX ls => LMAX (List.map f ls)

  structure Sort = RedPrlParamSort

  val arity =
    fn DIM0 => (DIM0, DIM)
     | DIM1 => (DIM1, DIM)
     | LCONST i => (LCONST i, LVL)
     | LABOVE (_, i) => (LABOVE (LVL, i), LVL)
     | LMAX ls => (LMAX (List.map (fn _ => LVL) ls), LVL)

  fun eq f =
    fn (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | (LCONST i0, LCONST i1) => i0 = i1
     | (LABOVE (l0, i0), LABOVE (l1, i1)) => f (l0, l1) andalso i0 = i1
     | (LMAX ls0, LMAX ls1) => ListPair.allEq f (ls0, ls1)
     | _ => false

  fun toString f =
    fn DIM0 => "0"
     | DIM1 => "1"
     | LCONST i => IntInf.toString i
     | LABOVE (l, i) => "labove{" ^ f l ^ "}"
     | LMAX ls => "lmax{" ^ String.concatWith "," (List.map f ls) ^ "}"

  fun join zer red =
    fn DIM0 => zer
     | DIM1 => zer
     | LCONST _ => zer
     | LABOVE (l, _) => red (zer, l)
     | LMAX ls => List.foldl red zer ls
end

structure RedPrlParameterTerm = AbtParameterTerm (RedPrlParameter)


structure RedPrlArity = ListAbtArity (structure PS = RedPrlParamSort and S = RedPrlSort)


structure RedPrlKind =
struct
  (*
   * DISCRETE < KAN < HCOM < CUBICAL
   *                < COE  <
   *
   * and KAN = meet (HCOM, COE)
   *)

  (* Please keep the following invariants when adding new kinds:
   *
   * (1) All judgments should still be closed under any substitution! In
   *     particular, the property that a type A has kind K is closed under any
   *     substitution.
   * (2) If two types are related with respect to a stronger kind (like KAN),
   *     then they are related with respect to a weaker kind (like CUBICAL).
   *     A stronger kind might demand more things to be equal. For example,
   *     the equality between two types with respect to KAN means that they
   *     are equally Kan, while the equality with respect to CUBICAL only says
   *     they are equal cubical pretypes.
   * (3) The PER associated with A should *never* depend on its kind. Kinds
   *     should be properties of (the PER of) A.
   * (4) We say KAN = meet (HCOM, COE) because if two types are equally "HCOM"
   *     and equally "COE" then they are equally Kan. Always remember to check
   *     the binary cases.
   *)
  datatype kind = DISCRETE | KAN | HCOM | COE | CUBICAL

  val COM = KAN

  val toString =
    fn DISCRETE => "discrete"
     | KAN => "kan"
     | HCOM => "hcom"
     | COE => "coe"
     | CUBICAL => "cubical"

  local
    structure Internal :
    (* this could be the new meet semi-lattice *)
    sig
      type t = kind

      val top : t
      val <= : t * t -> bool
      val meet : t * t -> t

      (* greatestMeetComplement (a, b) is the greatest element c
       * such that meet (b, c) <= a *)
      val greatestMeetComplement : t * t -> t
    end
    =
    struct
      type t = kind
      val top = CUBICAL

      val meet =
        fn (DISCRETE, _) => DISCRETE
         | (_, DISCRETE) => DISCRETE
         | (KAN, _) => KAN
         | (_, KAN) => KAN
         | (HCOM, COE) => KAN
         | (COE, HCOM) => KAN
         | (HCOM, _) => HCOM
         | (_, HCOM) => HCOM
         | (COE, _) => COE
         | (_, COE) => COE
         | (CUBICAL, CUBICAL) => CUBICAL

      val greatestMeetComplement =
        fn (_, DISCRETE) => top
         | (DISCRETE, _) => DISCRETE
         | (_, KAN) => top
         | (KAN, HCOM) => COE
         | (KAN, COE) => HCOM
         | (KAN, _) => KAN
         | (COE, HCOM) => COE
         | (HCOM, COE) => HCOM
         | (_, HCOM) => top
         | (HCOM, _) => HCOM
         | (_, COE) => top
         | (COE, _) => COE
         | (CUBICAL, CUBICAL) => top

      fun op <= (a, b) = greatestMeetComplement (b, a) = top
    end
  in
    open Internal
  end

  fun greatestMeetComplement' (a, b) =
    let val gmr = greatestMeetComplement (a, b)
    in if gmr = top then NONE else SOME gmr
    end
end

structure RedPrlOpData =
struct
  open RedPrlSortData
  structure P = RedPrlParameterTerm
  structure K = RedPrlKind
  type psort = RedPrlSortData.param_sort
  type kind = RedPrlKind.kind

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
   (* equality *)
   | EQUALITY

   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ of psort list | MTAC_ORELSE | MTAC_REC
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH of int | MTAC_FOCUS of int
   | MTAC_HOLE of string option
   | TAC_MTAC

   (* primitive rules *)
   | RULE_ID | RULE_AUTO_STEP | RULE_SYMMETRY | RULE_EXACT of sort | RULE_HEAD_EXP
   | RULE_CUT
   | RULE_PRIM of string

   (* development calculus terms *)
   | DEV_DFUN_INTRO of unit dev_pattern list
   | DEV_PATH_INTRO of int | DEV_RECORD_INTRO of string list
   | DEV_LET
   | DEV_MATCH of sort * int list
   | DEV_MATCH_CLAUSE of sort
   | DEV_QUERY_GOAL
   | DEV_PRINT of sort

   | JDG_TERM of sort
   | JDG_PARAM_SUBST of RedPrlParamSort.t list * sort

  type 'a equation = 'a P.term * 'a P.term
  type 'a dir = 'a P.term * 'a P.term

  datatype 'a poly_operator =
     FCOM of 'a dir * 'a equation list
   | LOOP of 'a P.term
   | PATH_APP of 'a P.term
   | UNIVERSE of 'a P.term * kind
   | HCOM of 'a dir * 'a equation list
   | COE of 'a dir
   | COM of 'a dir * 'a equation list
   | CUST of 'a * ('a P.term * psort option) list * RedPrlArity.t option

   | PAT_META of 'a * sort * ('a P.term * psort) list * sort list
   | HYP_REF of 'a * sort
   | PARAM_REF of psort * 'a P.term

   | RULE_ELIM of 'a
   | RULE_UNFOLD of 'a
   | DEV_BOOL_ELIM of 'a
   | DEV_S1_ELIM of 'a

   | DEV_APPLY_LEMMA of 'a * ('a P.term * psort option) list * RedPrlArity.t option * unit dev_pattern * int
   | DEV_APPLY_HYP of 'a * unit dev_pattern * int
   | DEV_USE_HYP of 'a * int
   | DEV_USE_LEMMA of 'a * ('a P.term * psort option) list * RedPrlArity.t option * int

   (* When the first argument is NONE, the following four are actually MONO,
    * but it seems better to treat them uniformly as POLY. *)
   | JDG_EQ of 'a P.term option * kind
   | JDG_TRUE of 'a P.term option * kind
   | JDG_EQ_TYPE of 'a P.term option * kind
   | JDG_SYNTH of 'a P.term option * kind

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
    fn PAT_VAR _ => [HYP]
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
     | INT_REC => [[] * [] <> EXP, [] * [] <> EXP, [] * [EXP, EXP] <> EXP, [] * [] <> EXP, [] * [EXP, EXP] <> EXP] ->> EXP

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

     | EQUALITY => [[] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> EXP

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
     | DEV_LET => [[] * [] <> JDG, [] * [] <> TAC, [HYP] * [] <> TAC] ->> TAC

     | DEV_MATCH (tau, ns) => ([] * [] <> tau) :: List.map (fn n => List.tabulate (n, fn _ => META_NAME) * [] <> MATCH_CLAUSE tau) ns ->> TAC
     | DEV_MATCH_CLAUSE tau => [[] * [] <> tau, [] * [] <> TAC] ->> MATCH_CLAUSE tau
     | DEV_QUERY_GOAL => [[] * [JDG] <> TAC] ->> TAC
     | DEV_PRINT tau => [[] * [] <> tau] ->> TAC

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
       | UNIVERSE _ => [] ->> EXP

       | HCOM params => arityHcom params
       | COE _ => [[DIM] * [] <> EXP, [] * [] <> EXP] ->> EXP
       | COM params => arityCom params
       | CUST (_, _, ar) => Option.valOf ar

       | PAT_META (_, tau, _, taus) => List.map (fn tau => [] * [] <> tau) taus ->> tau
       | HYP_REF (_, tau) => [] ->> tau
       | PARAM_REF (sigma, _) => [] ->> PARAM_EXP sigma

       | RULE_ELIM _ => [] ->> TAC
       | RULE_UNFOLD _ => [] ->> TAC
       | DEV_BOOL_ELIM _ => [[] * [] <> TAC, [] * [] <> TAC] ->> TAC
       | DEV_S1_ELIM _ => [[] * [] <> TAC, [DIM] * [] <> TAC] ->> TAC
       | DEV_APPLY_HYP (_, pat, n) => List.tabulate (n, fn _ => [] * [] <> TAC) @ [devPatternSymValence pat * [] <> TAC] ->> TAC
       | DEV_USE_HYP (_, n) => List.tabulate (n, fn _ => [] * [] <> TAC) ->> TAC
       | DEV_APPLY_LEMMA (_, _, ar, pat, n) => 
         let
           val (vls, tau) = Option.valOf ar
         in
           vls @ List.tabulate (n, fn _ => [] * [] <> TAC) @ [devPatternSymValence pat * [] <> TAC] ->> TAC
         end
       | DEV_USE_LEMMA (_, _, ar, n) => 
         let
           val (vls, tau) = Option.valOf ar
         in
           vls @ List.tabulate (n, fn _ => [] * [] <> TAC) ->> TAC
         end

       | JDG_EQ _ => [[] * [] <> EXP, [] * [] <> EXP, [] * [] <> EXP] ->> JDG
       | JDG_TRUE _ => [[] * [] <> EXP] ->> JDG
       | JDG_EQ_TYPE _ => [[] * [] <> EXP, [] * [] <> EXP] ->> JDG
       | JDG_SYNTH _ => [[] * [] <> EXP] ->> JDG
  end

  val arity =
    fn MONO th => arityMono th
     | POLY th => arityPoly th

  local
    val dimSupport =
      fn P.VAR a => [(a, DIM)]
       | P.APP t => P.freeVars t

    val levelSupport =
      fn P.VAR a => [(a, LVL)]
       | P.APP t => P.freeVars t

    fun optSupport f =
      fn NONE => []
       | SOME l => f l

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

    fun paramsSupport' ps =
      ListMonad.bind
        (fn (P.VAR a, tau) => [(a, tau)]
          | (P.APP t, _) => P.freeVars t)
        ps
  in
    val supportPoly =
      fn FCOM params => comSupport params
       | LOOP r => dimSupport r
       | PATH_APP r => dimSupport r
       | UNIVERSE (l, _) => levelSupport l
       | HCOM params => comSupport params
       | COE dir => spanSupport dir
       | COM params => comSupport params
       | CUST (opid, ps, _) => (opid, OPID) :: paramsSupport ps

       | PAT_META (x, _, ps, _) => (x, META_NAME) :: paramsSupport' ps
       | HYP_REF (a, _) => [(a, HYP)]
       | PARAM_REF (sigma, r) => paramsSupport [(r, SOME sigma)]

       | RULE_ELIM a => [(a, HYP)]
       | RULE_UNFOLD a => [(a, OPID)]
       | DEV_BOOL_ELIM a => [(a, HYP)]
       | DEV_S1_ELIM a => [(a, HYP)]
       | DEV_APPLY_HYP (a, _, _) => [(a, HYP)]
       | DEV_USE_HYP (a, _) => [(a, HYP)]
       | DEV_APPLY_LEMMA (opid, ps, _, _, _) => (opid, OPID) :: paramsSupport ps
       | DEV_USE_LEMMA (opid, ps, _, _) => (opid, OPID) :: paramsSupport ps

       | JDG_EQ (l, _) => optSupport levelSupport l
       | JDG_TRUE (l, _) => optSupport levelSupport l
       | JDG_EQ_TYPE (l, _) => optSupport levelSupport l
       | JDG_SYNTH (l, _) => optSupport levelSupport l
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

    fun optEq f =
      fn (NONE, NONE) => true
       | (SOME v1, SOME v2) => f (v1, v2)
       | _ => false
  in
    fun eqPoly f =
      fn (FCOM (dir1, eqs1), t) =>
         (case t of
             FCOM (dir2, eqs2) => spanEq f (dir1, dir2) andalso spansEq f (eqs1, eqs2)
           | _ => false)
       | (LOOP r, t) => (case t of LOOP r' => P.eq f (r, r') | _ => false)
       | (PATH_APP r, t) => (case t of PATH_APP r' => P.eq f (r, r') | _ => false)
       | (UNIVERSE (l, k), t) => (case t of UNIVERSE (l', k') => P.eq f (l, l') andalso k = k' | _ => false)
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

       | (PAT_META (x1, tau1, ps1, taus1), t) => 
         (case t of 
             PAT_META (x2, tau2, ps2, taus2) => f (x1, x2) andalso tau1 = tau2 andalso paramsEq f (ps1, ps2) andalso taus1 = taus2
           | _ => false)
       | (HYP_REF (a, _), t) => (case t of HYP_REF (b, _) => f (a, b) | _ => false)
       | (PARAM_REF (sigma1, r1), t) => (case t of PARAM_REF (sigma2, r2) => sigma1 = sigma2 andalso P.eq f (r1, r2) | _ => false)

       | (RULE_ELIM a, t) => (case t of RULE_ELIM b => f (a, b) | _ => false)
       | (RULE_UNFOLD a, t) => (case t of RULE_UNFOLD b => f (a, b) | _ => false)
       | (DEV_BOOL_ELIM a, t) => (case t of DEV_BOOL_ELIM b => f (a, b) | _ => false)
       | (DEV_S1_ELIM a, t) => (case t of DEV_S1_ELIM b => f (a, b) | _ => false)
       | (DEV_APPLY_HYP (a, pat, n), t) => (case t of DEV_APPLY_HYP (b, pat', n') => f (a, b) andalso pat = pat' andalso n = n' | _ => false)
       | (DEV_USE_HYP (a, n), t) => (case t of DEV_USE_HYP (b, n') => f (a, b) andalso n = n' | _ => false)
       | (DEV_APPLY_LEMMA (opid1, ps1, _, pat1, n1), t) =>
         (case t of
             DEV_APPLY_LEMMA (opid2, ps2, _, pat2, n2) => f (opid1, opid2) andalso paramsEq f (ps1, ps2) andalso pat1 = pat2 andalso n1 = n2
           | _ => false)
       | (DEV_USE_LEMMA (opid1, ps1, _, n1), t) =>
         (case t of
             DEV_USE_LEMMA (opid2, ps2, _, n2) => f (opid1, opid2) andalso paramsEq f (ps1, ps2) andalso n1 = n2
           | _ => false)

       | (JDG_EQ (l, k), t) =>
         (case t of
             JDG_EQ (l', k') => optEq (P.eq f) (l, l') andalso k = k'
           | _ => false)
       | (JDG_TRUE (l, k), t) =>
         (case t of
             JDG_TRUE (l', k') => optEq (P.eq f) (l, l') andalso k = k'
           | _ => false)
       | (JDG_EQ_TYPE (l, k), t) =>
         (case t of
             JDG_EQ_TYPE (l', k') => optEq (P.eq f) (l, l') andalso k = k'
           | _ => false)
       | (JDG_SYNTH (l, k), t) =>
         (case t of
             JDG_SYNTH (l', k') => optEq (P.eq f) (l, l') andalso k = k'
           | _ => false)

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

     | EQUALITY => "equality"

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
     | DEV_LET => "let"
     | DEV_MATCH _ => "dev-match"
     | DEV_MATCH_CLAUSE _ => "dev-match-clause"
     | DEV_QUERY_GOAL => "dev-query-goal"
     | DEV_PRINT _ => "dev-print"

     | JDG_TERM tau => RedPrlSort.toString tau
     | JDG_PARAM_SUBST _ => "param-subst"

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
       | UNIVERSE (l, k) => "universe{" ^ P.toString f l ^ "," ^ K.toString k ^ "}"
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

       | PAT_META (x, _, ps, _) =>
           "?" ^ f x ^ "{" ^ paramsToString f ps ^ "}"
       | HYP_REF (a, _) => "hyp-ref{" ^ f a ^ "}"
       | PARAM_REF (_, r) => "param-ref{" ^ P.toString f r ^ "}"

       | RULE_ELIM a => "elim{" ^ f a ^ "}"
       | RULE_UNFOLD a => "unfold{" ^ f a ^ "}"
       | DEV_BOOL_ELIM a => "bool-elim{" ^ f a ^ "}"
       | DEV_S1_ELIM a => "s1-elim{" ^ f a ^ "}"
       | DEV_APPLY_HYP (a, _, _) => "apply-hyp{" ^ f a ^ "}"
       | DEV_USE_HYP (a, _) => "use-hyp{" ^ f a ^ "}"
       | DEV_APPLY_LEMMA (opid, ps, _, _, _) => "apply-lemma{" ^ f opid ^ "}{" ^ paramsToString f ps ^ "}"
       | DEV_USE_LEMMA (opid, ps, _, _) => "use-lemma{" ^ f opid ^ "}{" ^ paramsToString f ps ^ "}"

       | JDG_EQ _ => "eq"
       | JDG_TRUE _ => "true"
       | JDG_EQ_TYPE _ => "eq-type"
       | JDG_SYNTH _ => "synth"
  end

  fun toString f =
    fn MONO th => toStringMono th
     | POLY th => toStringPoly f th

  local
    fun passSort sigma f =
      fn u => f (u, sigma)

    fun mapOpt f =
      fn NONE => NONE
       | SOME p => SOME (f p)

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

    fun mapParams' (f : 'a * psort -> 'b P.term) =
      List.map
        (fn (p, tau) =>
           let
             val q = P.bind (passSort tau f) p
             val _ = P.check tau q
           in
             (q, tau)
           end)

    fun mapSym f a =
      case f a of
         P.VAR a' => a'
       | P.APP _ => raise Fail "Expected symbol, but got application"
  in
    fun mapPolyWithSort f =
      fn FCOM (dir, eqs) => FCOM (mapSpan f dir, mapSpans f eqs)
       | LOOP r => LOOP (P.bind (passSort DIM f) r)
       | PATH_APP r => PATH_APP (P.bind (passSort DIM f) r)
       | UNIVERSE (l, k) => UNIVERSE (P.bind (passSort LVL f) l, k)
       | HCOM (dir, eqs) => HCOM (mapSpan f dir, mapSpans f eqs)
       | COE dir => COE (mapSpan f dir)
       | COM (dir, eqs) => COM (mapSpan f dir, mapSpans f eqs)
       | CUST (opid, ps, ar) => CUST (mapSym (passSort OPID f) opid, mapParams f ps, ar)

       | PAT_META (x, tau, ps, taus) => PAT_META (mapSym (passSort META_NAME f) x, tau, mapParams' f ps, taus)
       | HYP_REF (a, tau) => HYP_REF (mapSym (passSort HYP f) a, tau)
       | PARAM_REF (sigma, r) => PARAM_REF (sigma, P.bind (passSort sigma f) r)

       | RULE_ELIM a => RULE_ELIM (mapSym (passSort HYP f) a)
       | RULE_UNFOLD a => RULE_UNFOLD (mapSym (passSort OPID f) a)
       | DEV_BOOL_ELIM a => DEV_BOOL_ELIM (mapSym (passSort HYP f) a)
       | DEV_S1_ELIM a => DEV_S1_ELIM (mapSym (passSort HYP f) a)
       | DEV_APPLY_LEMMA (opid, ps, ar, pat, n) => DEV_APPLY_LEMMA (mapSym (passSort OPID f) opid, mapParams f ps, ar, pat, n)
       | DEV_APPLY_HYP (a, pat, spine) => DEV_APPLY_HYP (mapSym (passSort HYP f) a, pat, spine)
       | DEV_USE_HYP (a, n) => DEV_USE_HYP (mapSym (passSort HYP f) a, n)
       | DEV_USE_LEMMA (opid, ps, ar, n) => DEV_USE_LEMMA (mapSym (passSort OPID f) opid, mapParams f ps, ar, n)

       | JDG_EQ (l, k) => JDG_EQ (mapOpt (P.bind (passSort LVL f)) l, k)
       | JDG_TRUE (l, k) =>  JDG_TRUE (mapOpt (P.bind (passSort LVL f)) l, k)
       | JDG_EQ_TYPE (l, k) =>  JDG_EQ_TYPE (mapOpt (P.bind (passSort LVL f)) l, k)
       | JDG_SYNTH (l, k) =>  JDG_SYNTH (mapOpt (P.bind (passSort LVL f)) l, k)
  end

  fun mapWithSort f =
    fn MONO th => MONO th
     | POLY th => POLY (mapPolyWithSort f th)

  fun map f = 
    mapWithSort (fn (u, _) => f u)
end
