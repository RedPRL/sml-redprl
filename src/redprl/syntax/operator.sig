structure RedPrlOpData =
struct
  type opid = MlId.t
  type conid = string

  open RedPrlSort
  structure K = RedPrlKind
  type kind = RedPrlKind.kind

  datatype 'a dev_pattern = 
     PAT_VAR of 'a
   | PAT_TUPLE of (string * 'a dev_pattern) list

  datatype operator =
   (* the trivial realizer of sort EXP for types lacking interesting
    * computational content. This is the "ax(iom)" in Nuprl. *)
     AX
   (* bool *)
   | BOOL | TT | FF | IF
   (* natural numbers *)
   | NAT | ZERO | SUCC | NAT_REC
   (* integers *)
   | INT | POS | NEGSUCC | INT_REC
   (* empty type *)
   | VOID
   (* circle *)
   | S1 | BASE | LOOP | S1_REC
   (* function: lambda and app *)
   | FUN | LAM | APP
   (* record and tuple *)
   | RECORD of string list | TUPLE of string list | PROJ of string | TUPLE_UPDATE of string
   (* path: path abstraction and application *)
   | PATH | ABS | DIM_APP
   (* lines: paths without fixed endpoints *)
   | LINE
   (* pushout *)
   | PUSHOUT | LEFT | RIGHT | GLUE | PUSHOUT_REC
   (* coequalizer *)
   | COEQUALIZER | CECOD | CEDOM | COEQUALIZER_REC

   (* inductive types *)
   | IND_FAM_BASE of conid list
   | IND_FAM_LAM
   | IND_FAM_LINE

   | IND_SPECTYPE_SELF
   | IND_SPECTYPE_FUN

   | IND_SPEC_INTRO of conid
   | IND_SPEC_FCOM | IND_SPEC_LAM | IND_SPEC_APP

   | IND_CONSTR_LAM | IND_CONSTR_SPEC_LAM | IND_CONSTR_LINE
   | IND_CONSTR_BDRY_VEC | IND_CONSTR_DISCRETE

   | IND_TYPE of opid * RedPrlArity.valence list option
   | IND_INTRO of (opid * RedPrlArity.valence list option) * conid
   | IND_REC of (opid * RedPrlArity.valence list option) * RedPrlArity.Vl.bindings list option

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
   | MK_TUBE of sort
   | MK_BDRY of sort
   | MK_VEC of sort * int

   (* level expressions *)
   | LCONST of IntInf.int
   | LPLUS of IntInf.int
   | LMAX

   | KCONST of kind

   | JDG_TRUE
   | JDG_EQ_TYPE
   | JDG_SUB_TYPE
   | JDG_SUB_KIND
   | JDG_SYNTH
   | JDG_TERM of sort
   | JDG_IND_SPEC
   | JDG_EQ_IND_SPECTYPE
   | JDG_EQ_IND_SPEC

   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ | MTAC_ORELSE
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH | MTAC_FOCUS of int
   | MTAC_HOLE of string option
   | TAC_FAIL
   | TAC_MTAC

   | TAC_ID | TAC_AUTO_STEP | TAC_SYMMETRY | RULE_EXACT
   | RULE_CUT
   | RULE_PRIM of string
   | TAC_ELIM
   | TAC_REWRITE
   | TAC_REDUCE_ALL
   | TAC_REDUCE
   | TAC_REDUCE_PART
   | TAC_ASSUMPTION
   | TAC_POP of sort list
   | TAC_PUSH

   (* development calculus terms *)
   | DEV_FUN_INTRO of unit dev_pattern list
   | DEV_PATH_INTRO of int | DEV_RECORD_INTRO of string list
   | DEV_CLAIM of sort option
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
   
   | ACC_WHOLE
   | ACC_TYPE
   | ACC_LEFT
   | ACC_RIGHT

   | PAT_META of sort
 
   | CUST of opid * RedPrlArity.t option
   | TAC_UNFOLD_ALL of opid list
   | TAC_UNFOLD of opid list
   | TAC_UNFOLD_PART of opid list

   | DEV_USE_LEMMA
   | DEV_APPLY_LEMMA of unit dev_pattern
end

signature REDPRL_OPERATOR = 
sig
  datatype sort = datatype RedPrlSort.sort
  datatype operator = datatype RedPrlOpData.operator
  datatype dev_pattern = datatype RedPrlOpData.dev_pattern
  
  include ABT_OPERATOR
    where type t = operator
    where type Ar.Vl.S.t = sort

  (* TODO: where should this go? *)
  val indexToLabel : int -> string
end
