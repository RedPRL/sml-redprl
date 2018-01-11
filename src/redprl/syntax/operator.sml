structure ArityNotation =
struct
  fun op|: (a, b) = (a, b)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure RedPrlOperator : REDPRL_OPERATOR =
struct
  structure Ar = RedPrlArity

  open RedPrlOpData
  open ArityNotation infix <> ->> |:

  type t = operator

  (* where should this function go? *)
  fun indexToLabel i = "proj" ^ Int.toString (i + 1)  

  val rec devPatternValence = 
    fn PAT_VAR _ => [EXP]
     | PAT_TUPLE pats => List.concat (List.map (devPatternValence o #2) pats)

  val arity =
    fn AX => [] ->> EXP

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

     | PATH => [[DIM] |: EXP, [] |: EXP, [] |: EXP] ->> EXP
     | LINE => [[DIM] |: EXP] ->> EXP
     | ABS => [[DIM] |: EXP] ->> EXP
     | DIM_APP => [[] |: EXP, [] |: DIM] ->> EXP

     | PUSHOUT => [[] |: EXP, [] |: EXP, [] |: EXP, [EXP] |: EXP, [EXP] |: EXP] ->> EXP
     | LEFT => [[] |: EXP] ->> EXP
     | RIGHT => [[] |: EXP] ->> EXP
     | GLUE => [[] |: DIM, [] |: EXP, [] |: EXP, [] |: EXP] ->> EXP
     | PUSHOUT_REC => [[EXP] |: EXP, [] |: EXP, [EXP] |: EXP, [EXP] |: EXP, [DIM, EXP] |: EXP] ->> EXP

     | COEQUALIZER => [[] |: EXP, [] |: EXP, [EXP] |: EXP, [EXP] |: EXP] ->> EXP
     | CECOD => [[] |: EXP] ->> EXP
     | CEDOM => [[] |: DIM, [] |: EXP, [] |: EXP, [] |: EXP] ->> EXP
     | COEQUALIZER_REC => [[EXP] |: EXP, [] |: EXP, [EXP] |: EXP, [DIM, EXP] |: EXP] ->> EXP

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

     | KCONST _ => [] ->> KND


     | JDG_TRUE => [[] |: EXP] ->> JDG
     | JDG_EQ_TYPE => [[] |: KND, [] |: EXP, [] |: EXP] ->> JDG
     | JDG_SUB_TYPE => [[] |: EXP, [] |: EXP] ->> JDG
     | JDG_SUB_KIND => [[] |: KND, [] |: EXP] ->> JDG
     | JDG_SYNTH => [[] |: EXP] ->> JDG

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
     | TAC_FAIL => [] ->> TAC
     | TAC_MTAC => [[] |: MTAC] ->> TAC

     | TAC_ID => [] ->> TAC
     | TAC_AUTO_STEP => [] ->> TAC
     | TAC_SYMMETRY => [] ->> TAC
     | RULE_EXACT => [[] |: ANY] ->> TAC
     | TAC_REDUCE_ALL => [] ->> TAC
     | TAC_REDUCE => [[] |: VEC SEL] ->> TAC
     | TAC_REDUCE_PART => [[] |: SEL, [] |: VEC ACC] ->> TAC

     | RULE_CUT => [[] |: JDG] ->> TAC
     | RULE_PRIM _ => [] ->> TAC
     | TAC_ELIM => [[] |: ANY] ->> TAC
     | TAC_REWRITE => [[] |: SEL, [] |: ACC, [] |: EXP] ->> TAC

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
     
     | ACC_WHOLE => [] ->> ACC
     | ACC_TYPE => [] ->> ACC
     | ACC_LEFT => [] ->> ACC
     | ACC_RIGHT => [] ->> ACC

     | PAT_META tau => [[] |: META_NAME, [] |: VEC ANY] ->> tau

     | JDG_TERM _ => [] ->> JDG
     | CUST (_, ar) => Option.valOf ar
     | TAC_UNFOLD_ALL _ => [] ->> TAC
     | TAC_UNFOLD _ => [[] |: VEC SEL] ->> TAC
     | DEV_APPLY_LEMMA pat => [[] |: ANY, [] |: VEC TAC, devPatternValence pat |: TAC] ->> TAC
     | DEV_USE_LEMMA => [[] |: ANY, [] |: VEC TAC] ->> TAC

  fun eq (th1, th2) = th1 = th2

  val opidsToString =
   ListUtil.joinWith MlId.toString ","

  val toString =
    fn AX => "ax"

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

     | PATH => "path"
     | LINE => "line"
     | ABS => "abs"
     | DIM_APP => "path-app"

     | PUSHOUT => "pushout"
     | LEFT => "left"
     | RIGHT => "right"
     | GLUE => "glue"
     | PUSHOUT_REC => "pushout-rec"

     | COEQUALIZER => "coeq"
     | CECOD => "cecod"
     | CEDOM => "cedom"
     | COEQUALIZER_REC => "coeq-rec"

     | UNIVERSE => "U"
     | V => "V"
     | VIN => "Vin"
     | VPROJ => "Vproj"

     | EQUALITY => "="

     | MK_ANY _ => "any"

     | DIM0 => "dim0"
     | DIM1 => "dim1"
     | MK_TUBE => "tube"
     | MK_BDRY => "bdry"
     | MK_VEC _ => "vec" 

     | LCONST i => "{lconst " ^ IntInf.toString i  ^ "}"
     | LPLUS i => "{lplus " ^ IntInf.toString i ^ "}"
     | LMAX => "lmax"

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
     | TAC_FAIL => "fail"
     | TAC_MTAC => "mtac"

     | TAC_ID => "id"
     | TAC_AUTO_STEP => "auto-step"
     | TAC_SYMMETRY => "symmetry"
     | RULE_EXACT => "exact"
     | TAC_REDUCE_ALL => "reduce-all"
     | TAC_REDUCE => "reduce"
     | TAC_REDUCE_PART => "reduce-parts"
     | RULE_CUT => "cut"
     | RULE_PRIM name => "refine{" ^ name ^ "}"
     | TAC_ELIM => "elim"
     | TAC_REWRITE => "rewrite"

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

     | ACC_WHOLE => "accessor-whole"
     | ACC_LEFT => "accessor-left"
     | ACC_RIGHT => "accessor-right"
     | ACC_TYPE => "accessor-type"

     | PAT_META _ => "pat-meta"

     | JDG_TRUE => "true"
     | JDG_EQ_TYPE => "eq-type"
     | JDG_SUB_TYPE => "sub-type"
     | JDG_SUB_KIND => "sub-kind"
     | JDG_SYNTH => "synth"
     | JDG_TERM tau => RedPrlSort.toString tau
     | CUST (opid, _) => MlId.toString opid
     | TAC_UNFOLD_ALL os => "unfold-all{" ^ opidsToString os ^ "}"
     | TAC_UNFOLD os => "unfold{" ^ opidsToString os ^ "}"
     | DEV_APPLY_LEMMA _ => "apply-lemma"
     | DEV_USE_LEMMA => "use-lemma"
end
