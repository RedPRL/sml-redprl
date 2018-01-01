structure RedPrlOpData =
struct
  type opid = string (* TODO: structured representation to allow namespacing!! *)

  open RedPrlSort
  structure K = RedPrlKind
  type kind = RedPrlKind.kind

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
   | PATH | ABS | DIM_APP
   (* lines: paths without fixed endpoints *)
   | LINE
   (* pushout *)
   | PUSHOUT | LEFT | RIGHT | GLUE | PUSHOUT_REC
   (* coequalizer *)
   | COEQUALIZER | CECOD | CEDOM | COEQUALIZER_REC
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

   | KCONST of kind

   | JDG_TRUE
   | JDG_EQ_TYPE
   | JDG_SUB_TYPE
   | JDG_SUB_KIND
   | JDG_SYNTH
   | JDG_TERM of sort


   (* primitive tacticals and multitacticals *)
   | MTAC_SEQ of sort list | MTAC_ORELSE | MTAC_REC
   | MTAC_REPEAT | MTAC_AUTO | MTAC_PROGRESS
   | MTAC_ALL | MTAC_EACH | MTAC_FOCUS of int
   | MTAC_HOLE of string option
   | TAC_FAIL
   | TAC_MTAC

   (* primitive rules *)
   | TAC_ID | TAC_AUTO_STEP | TAC_SYMMETRY | RULE_EXACT | TAC_REDUCE_ALL
   | RULE_CUT
   | RULE_PRIM of string
   | TAC_ELIM
   | TAC_REWRITE
   | TAC_REWRITE_HYP
   | TAC_REDUCE

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
   
   | ACC_WHOLE
   | ACC_TYPE
   | ACC_LEFT
   | ACC_RIGHT

   | PAT_META of sort
 
   | CUST of opid * RedPrlArity.t option
   | TAC_UNFOLD_ALL of opid list
   | TAC_UNFOLD of opid list
   | DEV_USE_LEMMA of opid * RedPrlArity.t option
   | DEV_APPLY_LEMMA of opid * RedPrlArity.t option * unit dev_pattern
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
