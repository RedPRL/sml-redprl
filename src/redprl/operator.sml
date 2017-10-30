structure RedPrlSortData =
struct
  datatype sort =
     EXP
   | TAC
   | MTAC
   | JDG
   | TRV
   | MATCH_CLAUSE
   | DIM | TUBE | BDRY
   | VEC of sort
   | LVL
   | KND
   | SEL
   | ANY
   | META_NAME

  val rec sortToString = 
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | JDG => "jdg"
     | TRV => "trv"
     | MATCH_CLAUSE => "match-clause"
     | DIM => "dim"
     | TUBE => "tube"
     | BDRY => "bdry"
     | VEC tau => "vec{" ^ sortToString tau ^ "}"
     | LVL => "lvl"
     | KND => "knd"
     | SEL => "sel"
     | ANY => "any"
     | META_NAME => "meta-name"
end

structure RedPrlSort : ABT_SORT =
struct
  open RedPrlSortData
  type t = sort
  val eq : t * t -> bool = op=
  val toString = sortToString
end

structure RedPrlArity = ListAbtArity (structure S = RedPrlSort)

structure RedPrlKind =
struct
  (*
   * DISCRETE < KAN < HCOM < STABLE
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
   *     then they are related with respect to a weaker kind (like STABLE).
   *     A stronger kind might demand more things to be equal. For example,
   *     the equality between two types with respect to KAN means that they
   *     are equally Kan, while the equality with respect to STABLE only says
   *     they are equal pretypes.
   * (3) The PER associated with A should *never* depend on its kind. Kinds
   *     should be properties of (the PER of) A.
   * (4) We say KAN = meet (HCOM, COE) because if two types are equally "HCOM"
   *     and equally "COE" then they are equally Kan. Always remember to check
   *     the binary cases.
   *)
  datatype kind = DISCRETE | KAN | HCOM | COE | STABLE

  val COM = KAN

  val toString =
    fn DISCRETE => "discrete"
     | KAN => "kan"
     | HCOM => "hcom"
     | COE => "coe"
     | STABLE => "stable"

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
      val top = STABLE

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
         | (STABLE, STABLE) => STABLE

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
         | (STABLE, STABLE) => NONE

      fun op <= (a, b) = residual (b, a) = NONE
    end
  in
    open Internal
  end
end

structure RedPrlOpData =
struct
  type opid = string (* TODO: structured representation to allow namespacing!! *)

  open RedPrlSortData
  structure K = RedPrlKind
  type kind = RedPrlKind.kind

  (* TODO: move elsewhere *)
  datatype 'a selector = IN_CONCL | IN_HYP of 'a

  datatype 'a dev_pattern = 
     PAT_VAR of 'a
   | PAT_TUPLE of (string * 'a dev_pattern) list

  datatype operator =
   (* the trivial realizer of sort TRV for judgments lacking interesting
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

   | FCOM | BOX | CAP | HCOM | GHCOM | COE | COM | GCOM

   | MK_ANY of sort option

   (* dimension expressions *)

   | DIM0
   | DIM1
   | MK_TUBE
   | MK_BDRY
   | MK_VEC of sort * int

   (* level expressions *)
   | LCONST of IntInf.int
   | LPLUS of IntInf.int
   | LMAX
   | LOMEGA

   | KCONST of kind

   | JDG_EQ
   | JDG_TRUE
   | JDG_EQ_TYPE
   | JDG_SUB_UNIVERSE
   | JDG_SYNTH
   | JDG_TERM of sort


   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ of sort list | MTAC_ORELSE | MTAC_REC
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH | MTAC_FOCUS of int
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
   | DEV_QUERY
   | DEV_PRINT
   | DEV_BOOL_ELIM
   | DEV_S1_ELIM
   | DEV_APPLY_HYP of unit dev_pattern
   | DEV_USE_HYP
   | DEV_INVERSION

   | SEL_CONCL
   | SEL_HYP

   | PAT_META of sort
 
   | CUST of opid * RedPrlArity.t option
   | RULE_UNFOLD_ALL of opid list
   | RULE_UNFOLD of opid list
   | DEV_USE_LEMMA of opid * RedPrlArity.t option
   | DEV_APPLY_LEMMA of opid * RedPrlArity.t option * unit dev_pattern

   (* where should this function go? *)
   fun indexToLabel i = "proj" ^ Int.toString (i + 1)
end

structure ArityNotation =
struct
  fun op|: (a, b) = (a, b)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure RedPrlOperator : ABT_OPERATOR =
struct
  structure Ar = RedPrlArity

  open RedPrlOpData
  open ArityNotation infix <> ->> |:

  type t = operator

  val rec devPatternValence = 
    fn PAT_VAR _ => [EXP]
     | PAT_TUPLE pats => List.concat (List.map (devPatternValence o #2) pats)

  val arity =
    fn TV => [] ->> TRV
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
     | BOX => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: VEC BDRY] ->> EXP
     | CAP => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | HCOM => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | GHCOM => [[] |: DIM, [] |: DIM, [] |: EXP, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | COE => [[] |: DIM, [] |: DIM, [DIM] |: EXP, [] |: EXP] ->> EXP
     | COM => [[] |: DIM, [] |: DIM, [DIM] |: EXP, [] |: EXP, [] |: VEC TUBE] ->> EXP
     | GCOM => [[] |: DIM, [] |: DIM, [DIM] |: EXP, [] |: EXP, [] |: VEC TUBE] ->> EXP

     | UNIVERSE => [[] |: LVL, [] |: KND] ->> EXP
     | V => [[] |: DIM, [] |: EXP, [] |: EXP, [] |: EXP] ->> EXP
     | VIN => [[] |: DIM, [] |: EXP, [] |: EXP] ->> EXP
     | VPROJ => [[] |: DIM, [] |: EXP, [] |: EXP] ->> EXP

     | EQUALITY => [[] |: EXP, [] |: EXP, [] |: EXP] ->> EXP

     | MK_ANY tau => [[] |: Option.valOf tau] ->> ANY

     | DIM0 => [] ->> DIM
     | DIM1 => [] ->> DIM
     | MK_TUBE => [[] |: DIM, [] |: DIM, [DIM] |: EXP] ->> TUBE
     | MK_BDRY => [[] |: DIM, [] |: DIM, [] |: EXP] ->> BDRY
     | MK_VEC (tau, n) => List.tabulate (n, fn _ => [] |: tau) ->> VEC tau

     | LCONST i => [] ->> LVL
     | LPLUS i => [[] |: LVL] ->> LVL
     | LMAX => [[] |: VEC LVL] ->> LVL
     | LOMEGA => [] ->> LVL

     | KCONST _ => [] ->> KND


     | JDG_EQ => [[] |: LVL, [] |: KND, [] |: EXP, [] |: EXP, [] |: EXP] ->> JDG
     | JDG_TRUE => [[] |: LVL, [] |: KND, [] |: EXP] ->> JDG
     | JDG_EQ_TYPE => [[] |: LVL, [] |: KND, [] |: EXP, [] |: EXP] ->> JDG
     | JDG_SUB_UNIVERSE => [[] |: LVL, [] |: KND, [] |: EXP] ->> JDG
     | JDG_SYNTH => [[] |: LVL, [] |: KND, [] |: EXP] ->> JDG

     | MTAC_SEQ sorts => [[] |: MTAC, sorts |: MTAC] ->> MTAC
     | MTAC_ORELSE => [[] |: MTAC, [] |: MTAC] ->> MTAC
     | MTAC_REC => [[MTAC] |: MTAC] ->> MTAC
     | MTAC_REPEAT => [[] |: MTAC] ->> MTAC
     | MTAC_AUTO => [] ->> MTAC
     | MTAC_PROGRESS => [[] |: MTAC] ->> MTAC
     | MTAC_ALL => [[] |: TAC] ->> MTAC
     | MTAC_EACH => [[] |: VEC TAC] ->> MTAC
     | MTAC_FOCUS _ => [[] |: TAC] ->> MTAC
     | MTAC_HOLE _ => [] ->> MTAC
     | TAC_MTAC => [[] |: MTAC] ->> TAC

     | RULE_ID => [] ->> TAC
     | RULE_AUTO_STEP => [] ->> TAC
     | RULE_SYMMETRY => [] ->> TAC
     | RULE_EXACT => [[] |: ANY] ->> TAC
     | RULE_REDUCE_ALL => [] ->> TAC
     | RULE_REDUCE => [[] |: VEC SEL] ->> TAC

     | RULE_CUT => [[] |: JDG] ->> TAC
     | RULE_PRIM _ => [] ->> TAC
     | RULE_ELIM => [[] |: ANY] ->> TAC
     | RULE_REWRITE => [[] |: SEL, [] |: EXP] ->> TAC
     | RULE_REWRITE_HYP => [[] |: SEL, [] |: ANY] ->> TAC

     | DEV_FUN_INTRO pats => [List.concat (List.map devPatternValence pats) |: TAC] ->> TAC
     | DEV_RECORD_INTRO lbls => List.map (fn _ => [] |: TAC) lbls ->> TAC
     | DEV_PATH_INTRO n => [List.tabulate (n, fn _ => DIM) |: TAC] ->> TAC
     | DEV_LET tau => [[] |: JDG, [] |: TAC, [Option.valOf tau] |: TAC] ->> TAC

     | DEV_MATCH ns => ([] |: ANY) :: List.map (fn n => List.tabulate (n, fn _ => META_NAME) |: MATCH_CLAUSE) ns ->> TAC
     | DEV_MATCH_CLAUSE => [[] |: ANY, [] |: TAC] ->> MATCH_CLAUSE
     | DEV_QUERY => [[] |: SEL, [JDG] |: TAC] ->> TAC
     | DEV_PRINT => [[] |: ANY] ->> TAC
     | DEV_BOOL_ELIM => [[] |: EXP, [] |: TAC, [] |: TAC] ->> TAC
     | DEV_S1_ELIM => [[] |: EXP, [] |: TAC, [DIM] |: TAC] ->> TAC
     | DEV_APPLY_HYP pat => [[] |: ANY, [] |: VEC TAC, devPatternValence pat |: TAC] ->> TAC
     | DEV_USE_HYP => [[] |: ANY, [] |: VEC TAC] ->> TAC
     | DEV_INVERSION => [] ->> TAC

     | SEL_HYP => [[] |: ANY] ->> SEL
     | SEL_CONCL => [] ->> SEL

     | PAT_META tau => [[] |: META_NAME, [] |: VEC ANY] ->> tau

     | JDG_TERM _ => [] ->> JDG
     | CUST (_, ar) => Option.valOf ar
     | RULE_UNFOLD_ALL _ => [] ->> TAC
     | RULE_UNFOLD _ => [[] |: VEC SEL] ->> TAC
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

  fun eq (th1, th2) = th1 = th2

  val opidsToString =
   ListUtil.joinWith (fn x => x) ","

  val toString =
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

     | RECORD lbls => "record{" ^ ListUtil.joinWith (fn s => s) "," lbls ^ "}"
     | TUPLE lbls => "tuple{" ^ ListUtil.joinWith (fn s => s) "," lbls ^ "}"
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
     | MK_BDRY => "bdry"
     | MK_VEC _ => "vec" 

     | LCONST i => "{lconst " ^ IntInf.toString i  ^ "}"
     | LPLUS i => "{lplus " ^ IntInf.toString i ^ "}"
     | LMAX => "lmax"
     | LOMEGA => "lomega"

     | KCONST k => RedPrlKind.toString k

     | MTAC_SEQ sorts => "seq{" ^ ListUtil.joinWith RedPrlSort.toString "," sorts ^ "}"
     | MTAC_ORELSE => "orelse"
     | MTAC_REC => "rec"
     | MTAC_REPEAT => "repeat"
     | MTAC_AUTO => "auto"
     | MTAC_PROGRESS => "multi-progress"
     | MTAC_ALL => "all"
     | MTAC_EACH => "each"
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
     | DEV_RECORD_INTRO lbls => "record-intro{" ^ ListUtil.joinWith (fn x => x) "," lbls ^ "}"
     | DEV_LET _ => "let"
     | DEV_MATCH _ => "dev-match"
     | DEV_MATCH_CLAUSE => "dev-match-clause"
     | DEV_QUERY => "dev-query"
     | DEV_PRINT => "dev-print"
     | DEV_BOOL_ELIM => "dev-bool-elim"
     | DEV_S1_ELIM => "dev-s1-elim"
     | DEV_APPLY_HYP _ => "apply-hyp"
     | DEV_USE_HYP => "use-hyp"
     | DEV_INVERSION => "inversion"

     | FCOM => "fcom"
     | BOX => "box"
     | CAP => "cap"
     | HCOM => "hcom"
     | GHCOM => "ghcom"
     | COE => "coe"
     | COM => "com"
     | GCOM => "com"

     | SEL_HYP => "select-hyp"
     | SEL_CONCL => "select-goal"
     | PAT_META _ => "pat-meta"

     | JDG_EQ => "eq"
     | JDG_TRUE => "true"
     | JDG_EQ_TYPE => "eq-type"
     | JDG_SUB_UNIVERSE => "sub-universe"
     | JDG_SYNTH => "synth"
     | JDG_TERM tau => RedPrlSort.toString tau
     | CUST (opid, _) => opid
     | RULE_UNFOLD_ALL os => "unfold-all{" ^ opidsToString os ^ "}"
     | RULE_UNFOLD os => "unfold{" ^ opidsToString os ^ "}"
     | DEV_APPLY_LEMMA (opid, _, _) => "apply-lemma{" ^ opid ^ "}"
     | DEV_USE_LEMMA (opid, _) => "use-lemma{" ^ opid ^ "}"
end
