structure RedPrlSortData =
struct
  datatype param_sort =
     META_NAME
   | OPID

  and sort =
     EXP
   | TAC
   | MTAC
   | JDG
   | TRIV
   | MATCH_CLAUSE
   | DIM | TUBE | BOUNDARY
   | VEC of sort
   | LVL
   | KIND
   | SELECTOR
   | ANY

  val rec sortToString = 
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | JDG => "jdg"
     | TRIV => "triv"
     | MATCH_CLAUSE => "match-clause"
     | DIM => "dim"
     | TUBE => "tube"
     | BOUNDARY => "boundary"
     | VEC tau => "vec{" ^ sortToString tau ^ "}"
     | LVL => "lvl"
     | KIND => "kind"
     | SELECTOR => "selector"
     | ANY => "any"

  and paramSortToString = 
    fn META_NAME => "meta-name"
     | OPID => "opid"
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
  open RedPrlSortData
  type t = param_sort
  val eq : t * t -> bool = op=
  val toString = paramSortToString
end

structure RedPrlParameter = AbtEmptyParameter (RedPrlParamSort)
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

      (* residual (a, b)
       *
       * Let c be the greatest element such that `meet (b, c) <= a`.
       * The return value is SOME c if c is not top, or NONE otherwise.
       * *)
      val residual : t * t -> t option
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

      val residual =
        fn (_, DISCRETE) => NONE
         | (DISCRETE, _) => SOME DISCRETE
         | (_, KAN) => NONE
         | (KAN, HCOM) => SOME COE
         | (KAN, COE) => SOME HCOM
         | (KAN, _) => SOME KAN
         | (COE, HCOM) => SOME COE
         | (HCOM, COE) => SOME HCOM
         | (_, HCOM) => NONE
         | (HCOM, _) => SOME HCOM
         | (_, COE) => NONE
         | (COE, _) => SOME COE
         | (CUBICAL, CUBICAL) => NONE

      fun op <= (a, b) = residual (b, a) = NONE
    end
  in
    open Internal
  end
end

structure RedPrlOpData =
struct
  open RedPrlSortData
  structure P = RedPrlParameterTerm
  structure K = RedPrlKind
  type psort = RedPrlSortData.param_sort
  type kind = RedPrlKind.kind

  (* TODO: move elsewhere *)
  datatype 'a selector = IN_CONCL | IN_HYP of 'a

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
   | S1 | BASE | LOOP | S1_REC
   (* function: lambda and app *)
   | FUN | LAM | APP
   (* record and tuple *)
   | RECORD of string list | TUPLE of string list | PROJ of string | TUPLE_UPDATE of string
   (* path: path abstraction and application *)
   | PATH_TY | PATH_ABS | PATH_APP
   (* equality *)
   | EQUALITY
   (* universe *)
   | UNIVERSE
   | V
   | VIN
   | VPROJ

   | FCOM | BOX | CAP | HCOM | COE | COM

   | MK_ANY of sort option

   (* dimension expressions *)

   | DIM0
   | DIM1
   | MK_TUBE
   | MK_BOUNDARY
   | MK_VEC of sort * int

   (* level expressions *)
   | LCONST of IntInf.int
   | LPLUS of IntInf.int
   | LMAX

   | KCONST of kind

   | JDG_EQ of bool
   | JDG_TRUE of bool 
   | JDG_EQ_TYPE of bool 
   | JDG_SUB_UNIVERSE of bool 
   | JDG_SYNTH of bool
   | JDG_TERM of sort


   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ of sort list | MTAC_ORELSE | MTAC_REC
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH of int | MTAC_FOCUS of int
   | MTAC_HOLE of string option
   | TAC_MTAC

   (* primitive rules *)
   | RULE_ID | RULE_AUTO_STEP | RULE_SYMMETRY | RULE_EXACT | RULE_REDUCE_ALL
   | RULE_CUT
   | RULE_PRIM of string
   | RULE_ELIM
   | RULE_REWRITE
   | RULE_REWRITE_HYP
   | RULE_REDUCE

   (* development calculus terms *)
   | DEV_FUN_INTRO of unit dev_pattern list
   | DEV_PATH_INTRO of int | DEV_RECORD_INTRO of string list
   | DEV_LET of sort option
   | DEV_MATCH of int list
   | DEV_MATCH_CLAUSE
   | DEV_QUERY_CONCL
   | DEV_PRINT
   | DEV_BOOL_ELIM
   | DEV_S1_ELIM
   | DEV_APPLY_HYP of unit dev_pattern
   | DEV_USE_HYP

   | SEL_CONCL
   | SEL_HYP

  datatype 'a poly_operator =
     CUST of 'a * RedPrlArity.t option
   | PAT_META of 'a * sort

   | RULE_UNFOLD_ALL of 'a list
   | RULE_UNFOLD of 'a list


   | DEV_USE_LEMMA of 'a * RedPrlArity.t option
   | DEV_APPLY_LEMMA of 'a * RedPrlArity.t option * unit dev_pattern

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
  fun op|: (a, b) = (([], a), b)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure RedPrlOperator : ABT_OPERATOR =
struct
  structure Ar = RedPrlArity

  open RedPrlOpData
  open ArityNotation infix <> ->> |:

  type 'a t = 'a operator

  val rec devPatternValence = 
    fn PAT_VAR _ => [EXP]
     | PAT_TUPLE pats => List.concat (List.map (devPatternValence o #2) pats)

  val arityMono =
    fn TV => [] ->> TRIV
     | AX => [] ->> EXP

     | BOOL => [] ->> EXP
     | TT => [] ->> EXP
     | FF => [] ->> EXP
     | IF => [[] |: EXP, [] |: EXP, [] |: EXP] ->> EXP

     | WBOOL => [] ->> EXP
     | WIF => [[EXP] |: EXP, [] |: EXP, [] |: EXP, [] |: EXP] ->> EXP

     | VOID => [] ->> EXP

     | NAT => [] ->> EXP
     | ZERO => [] ->> EXP
     | SUCC => [[] |: EXP] ->> EXP
     | NAT_REC => [[] |: EXP, [] |: EXP, [EXP, EXP] |: EXP] ->> EXP
     | INT => [] ->> EXP
     | NEGSUCC => [[] |: EXP] ->> EXP
     | INT_REC => [[] |: EXP, [] |: EXP, [EXP, EXP] |: EXP, [] |: EXP, [EXP, EXP] |: EXP] ->> EXP

     | S1 => [] ->> EXP
     | BASE => [] ->> EXP
     | LOOP => [[] |: DIM] ->> EXP
     | S1_REC => [[EXP] |: EXP, [] |: EXP, [] |: EXP, [DIM] |: EXP] ->> EXP

     | FUN => [[] |: EXP, [EXP] |: EXP] ->> EXP
     | LAM => [[EXP] |: EXP] ->> EXP
     | APP => [[] |: EXP, [] |: EXP] ->> EXP

     | RECORD lbls =>
       let
         val (_, valences) = List.foldr (fn (_, (taus, vls)) => (EXP :: taus, (taus |: EXP) :: vls)) ([], []) lbls
       in 
         List.rev valences ->> EXP
       end
     | TUPLE lbls => (map (fn _ => ([] |: EXP)) lbls) ->> EXP
     | PROJ lbl => [[] |: EXP] ->> EXP
     | TUPLE_UPDATE lbl => [[] |: EXP, [] |: EXP] ->> EXP

     | PATH_TY => [[DIM] |: EXP, [] |: EXP, [] |: EXP] ->> EXP
     | PATH_ABS => [[DIM] |: EXP] ->> EXP
     | PATH_APP => [[] |: EXP, [] |: DIM] ->> EXP

     | FCOM => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | BOX => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: VEC BOUNDARY] ->> EXP
     | CAP => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | HCOM => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | COE => [[] |: DIM, [] |: DIM, [DIM] |: EXP, [] |: EXP] ->> EXP
     | COM => [[] |: DIM, [] |: DIM, [DIM] |: EXP, [] |: EXP, [] |: VEC TUBE] ->> EXP

     | UNIVERSE => [[] |: LVL, [] |: KIND] ->> EXP
     | V => [[] |: DIM, [] |: EXP, [] |: EXP, [] |: EXP] ->> EXP
     | VIN => [[] |: DIM, [] |: EXP, [] |: EXP] ->> EXP
     | VPROJ => [[] |: DIM, [] |: EXP, [] |: EXP] ->> EXP

     | EQUALITY => [[] |: EXP, [] |: EXP, [] |: EXP] ->> EXP

     | MK_ANY tau => [[] |: Option.valOf tau] ->> ANY

     | DIM0 => [] ->> DIM
     | DIM1 => [] ->> DIM
     | MK_TUBE => [[] |: DIM, [] |: DIM, [DIM] |: EXP] ->> TUBE
     | MK_BOUNDARY => [[] |: DIM, [] |: DIM, [] |: EXP] ->> BOUNDARY
     | MK_VEC (tau, n) => List.tabulate (n, fn _ => [] |: tau) ->> VEC tau

     | LCONST i => [] ->> LVL
     | LPLUS i => [[] |: LVL] ->> LVL
     | LMAX => [[] |: VEC LVL] ->> LVL

     | KCONST _ => [] ->> KIND


     | JDG_EQ b => (if b then [[] |: LVL] else []) @ [[] |: KIND, [] |: EXP, [] |: EXP, [] |: EXP] ->> JDG
     | JDG_TRUE b => (if b then [[] |: LVL] else []) @ [[] |: KIND, [] |: EXP] ->> JDG
     | JDG_EQ_TYPE b => (if b then [[] |: LVL] else []) @ [[] |: KIND, [] |: EXP, [] |: EXP] ->> JDG
     | JDG_SUB_UNIVERSE b => (if b then [[] |: LVL] else []) @ [[] |: KIND, [] |: EXP] ->> JDG
     | JDG_SYNTH b => (if b then [[] |: LVL] else []) @ [[] |: KIND, [] |: EXP] ->> JDG

     | MTAC_SEQ sorts => [[] |: MTAC, sorts |: MTAC] ->> MTAC
     | MTAC_ORELSE => [[] |: MTAC, [] |: MTAC] ->> MTAC
     | MTAC_REC => [[MTAC] |: MTAC] ->> MTAC
     | MTAC_REPEAT => [[] |: MTAC] ->> MTAC
     | MTAC_AUTO => [] ->> MTAC
     | MTAC_PROGRESS => [[] |: MTAC] ->> MTAC
     | MTAC_ALL => [[] |: TAC] ->> MTAC
     | MTAC_EACH n =>
         let
           val tacs = List.tabulate (n, fn _ => [] |: TAC)
         in
           tacs ->> MTAC
         end
     | MTAC_FOCUS _ => [[] |: TAC] ->> MTAC
     | MTAC_HOLE _ => [] ->> MTAC
     | TAC_MTAC => [[] |: MTAC] ->> TAC

     | RULE_ID => [] ->> TAC
     | RULE_AUTO_STEP => [] ->> TAC
     | RULE_SYMMETRY => [] ->> TAC
     | RULE_EXACT => [[] |: ANY] ->> TAC
     | RULE_REDUCE_ALL => [] ->> TAC
     | RULE_REDUCE => [[] |: VEC SELECTOR] ->> TAC

     | RULE_CUT => [[] |: JDG] ->> TAC
     | RULE_PRIM _ => [] ->> TAC
     | RULE_ELIM => [[] |: ANY] ->> TAC
     | RULE_REWRITE => [[] |: SELECTOR, [] |: EXP] ->> TAC
     | RULE_REWRITE_HYP => [[] |: SELECTOR, [] |: ANY] ->> TAC

     | DEV_FUN_INTRO pats => [List.concat (List.map devPatternValence pats) |: TAC] ->> TAC
     | DEV_RECORD_INTRO lbls => List.map (fn _ => [] |: TAC) lbls ->> TAC
     | DEV_PATH_INTRO n => [List.tabulate (n, fn _ => DIM) |: TAC] ->> TAC
     | DEV_LET tau => [[] |: JDG, [] |: TAC, [Option.valOf tau] |: TAC] ->> TAC

     | DEV_MATCH ns => ([] |: ANY) :: List.map (fn n => List.tabulate (n, fn _ => META_NAME) * [] <> MATCH_CLAUSE) ns ->> TAC
     | DEV_MATCH_CLAUSE => [[] |: ANY, [] |: TAC] ->> MATCH_CLAUSE
     | DEV_QUERY_CONCL => [[JDG] |: TAC] ->> TAC
     | DEV_PRINT => [[] |: ANY] ->> TAC
     | DEV_BOOL_ELIM => [[] |: EXP, [] |: TAC, [] |: TAC] ->> TAC
     | DEV_S1_ELIM => [[] |: EXP, [] |: TAC, [DIM] |: TAC] ->> TAC
     | DEV_APPLY_HYP pat => [[] |: EXP, [] |: VEC TAC, devPatternValence pat |: TAC] ->> TAC
     | DEV_USE_HYP => [[] |: EXP, [] |: VEC TAC] ->> TAC

     | SEL_HYP => [[] |: ANY] ->> SELECTOR
     | SEL_CONCL => [] ->> SELECTOR

     | JDG_TERM _ => [] ->> JDG

  local
  in
    val arityPoly =
      fn CUST (_, ar) => Option.valOf ar
       | PAT_META (_, tau) => [[] |: VEC ANY] ->> tau
       | RULE_UNFOLD_ALL _ => [] ->> TAC
       | RULE_UNFOLD _ => [[] |: VEC SELECTOR] ->> TAC
       | DEV_APPLY_LEMMA (_, ar, pat) =>
         let
           val (vls, tau) = Option.valOf ar
         in
           vls @ [[] |: VEC TAC, devPatternValence pat |: TAC] ->> TAC
         end
       | DEV_USE_LEMMA (_, ar) => 
         let
           val (vls, tau) = Option.valOf ar
         in
           vls @ [[] |: VEC TAC] ->> TAC
         end
  end

  val arity =
    fn MONO th => arityMono th
     | POLY th => arityPoly th

  local
    fun opidsSupport os =
      List.map (fn name => (name, OPID)) os
  in
    val supportPoly =
      fn CUST (opid, _) => [(opid, OPID)]
       | PAT_META (x, _) => [(x, META_NAME)]
       | RULE_UNFOLD_ALL names => opidsSupport names
       | RULE_UNFOLD names => opidsSupport names
       | DEV_APPLY_LEMMA (opid, _, _) => [(opid, OPID)]
       | DEV_USE_LEMMA (opid,  _) => [(opid, OPID)]
  end

  val support =
    fn MONO _ => []
     | POLY th => supportPoly th

  local
    val optEq = OptionUtil.eq

    fun selectorEq f =
      fn (IN_CONCL, IN_CONCL) => true
       | (IN_HYP a, IN_HYP b) => f (a, b)
       | _ => false

    fun selectorsEq f = ListPair.allEq (selectorEq f)

    fun opidsEq f = ListPair.allEq f
  in
    fun eqPoly f =
      fn (CUST (opid1, _), t) =>
         (case t of
             CUST (opid2, _) => f (opid1, opid2)
           | _ => false)
       | (PAT_META (x1, tau1), t) => 
         (case t of 
             PAT_META (x2, tau2) => f (x1, x2) andalso tau1 = tau2
           | _ => false)
       | (RULE_UNFOLD_ALL os1, t) => (case t of RULE_UNFOLD_ALL os2 => opidsEq f (os1, os2) | _ => false)
       | (RULE_UNFOLD os1, t) => (case t of RULE_UNFOLD os2 => opidsEq f (os1, os2) | _ => false)
       | (DEV_APPLY_LEMMA (opid1, _, pat1), t) =>
         (case t of
             DEV_APPLY_LEMMA (opid2, _, pat2) => f (opid1, opid2) andalso pat1 = pat2
           | _ => false)
       | (DEV_USE_LEMMA (opid1, _), t) =>
         (case t of
             DEV_USE_LEMMA (opid2, _) => f (opid1, opid2)
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
     | LOOP => "loop"
     | S1_REC => "S1-rec"

     | FUN => "fun"
     | LAM => "lam"
     | APP => "app"

     | RECORD lbls => "record{" ^ ListSpine.pretty (fn s => s) "," lbls ^ "}"
     | TUPLE lbls => "tuple{" ^ ListSpine.pretty (fn s => s) "," lbls ^ "}"
     | PROJ lbl => "proj{" ^ lbl ^ "}"
     | TUPLE_UPDATE lbl => "update{" ^ lbl ^ "}"

     | PATH_TY => "path"
     | PATH_ABS => "abs"
     | PATH_APP => "path-app"

     | UNIVERSE => "U"
     | V => "V"
     | VIN => "Vin"
     | VPROJ => "Vproj"

     | EQUALITY => "equality"

     | MK_ANY _ => "any"

     | DIM0 => "dim0"
     | DIM1 => "dim1"
     | MK_TUBE => "tube"
     | MK_BOUNDARY => "boundary"
     | MK_VEC _ => "vec" 

     | LCONST i => "{lconst " ^ IntInf.toString i  ^ "}"
     | LPLUS i => "{lsuc " ^ IntInf.toString i ^ "}"
     | LMAX => "lmax"

     | KCONST k => RedPrlKind.toString k

     | MTAC_SEQ sorts => "seq{" ^ ListSpine.pretty RedPrlSort.toString "," sorts ^ "}"
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
     | RULE_EXACT => "exact"
     | RULE_REDUCE_ALL => "reduce-all"
     | RULE_REDUCE => "reduce"
     | RULE_CUT => "cut"
     | RULE_PRIM name => "refine{" ^ name ^ "}"
     | RULE_ELIM => "elim"
     | RULE_REWRITE => "rewrite"
     | RULE_REWRITE_HYP => "rewrite-hyp"

     | DEV_PATH_INTRO n => "path-intro{" ^ Int.toString n ^ "}"
     | DEV_FUN_INTRO pats => "fun-intro"
     | DEV_RECORD_INTRO lbls => "record-intro{" ^ ListSpine.pretty (fn x => x) "," lbls ^ "}"
     | DEV_LET _ => "let"
     | DEV_MATCH _ => "dev-match"
     | DEV_MATCH_CLAUSE => "dev-match-clause"
     | DEV_QUERY_CONCL => "dev-query-concl"
     | DEV_PRINT => "dev-print"
     | DEV_BOOL_ELIM => "dev-bool-elim"
     | DEV_S1_ELIM => "dev-s1-elim"
     | DEV_APPLY_HYP _ => "apply-hyp"
     | DEV_USE_HYP => "use-hyp"

     | FCOM => "fcom"
     | BOX => "box"
     | CAP => "cap"
     | HCOM => "hcom"
     | COM => "com"
     | COE => "coe"

     | SEL_HYP => "select-hyp"
     | SEL_CONCL => "select-goal"

     | JDG_EQ _ => "eq"
     | JDG_TRUE _ => "true"
     | JDG_EQ_TYPE _ => "eq-type"
     | JDG_SUB_UNIVERSE _ => "sub-universe"
     | JDG_SYNTH _ => "synth"
     | JDG_TERM tau => RedPrlSort.toString tau

  local
    fun opidsToString f =
      ListSpine.pretty f ","
  in
    fun toStringPoly f =
      fn CUST (opid, _) => f opid
       | PAT_META (x, _) => "%" ^ f x
       | RULE_UNFOLD_ALL os => "unfold-all{" ^ opidsToString f os ^ "}"
       | RULE_UNFOLD os => "unfold{" ^ opidsToString f os ^ "}"
       | DEV_APPLY_LEMMA (opid, _, _) => "apply-lemma{" ^ f opid ^ "}"
       | DEV_USE_LEMMA (opid, _) => "use-lemma{" ^ f opid ^ "}"
  end

  fun toString f =
    fn MONO th => toStringMono th
     | POLY th => toStringPoly f th

  local
    fun passSort sigma f =
      fn u => f (u, sigma)

    val mapOpt = Option.map

    fun mapSym f a =
      case f a of
         P.VAR a' => a'
       | P.APP _ => raise Fail "Expected symbol, but got application"

    fun mapSelector f =
      fn IN_CONCL => IN_CONCL
       | IN_HYP a => IN_HYP (f a)
  in
    fun mapPolyWithSort f =
      fn CUST (opid, ar) => CUST (mapSym (passSort OPID f) opid, ar)
       | PAT_META (x, tau) => PAT_META (mapSym (passSort META_NAME f) x, tau)
       | RULE_UNFOLD_ALL ns => RULE_UNFOLD_ALL (List.map (mapSym (passSort OPID f)) ns)
       | RULE_UNFOLD ns => RULE_UNFOLD (List.map (mapSym (passSort OPID f)) ns)
       | DEV_APPLY_LEMMA (opid, ar, pat) => DEV_APPLY_LEMMA (mapSym (passSort OPID f) opid, ar, pat)
       | DEV_USE_LEMMA (opid, ar) => DEV_USE_LEMMA (mapSym (passSort OPID f) opid, ar)
  end

  fun mapWithSort f =
    fn MONO th => MONO th
     | POLY th => POLY (mapPolyWithSort f th)

  fun map f = 
    mapWithSort (fn (u, _) => f u)
end
