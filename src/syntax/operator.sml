(* This is the sum type containing all the operators in JonPRL's
 * programming language. *)

structure RedPrlOperators =
struct
  structure Sort = RedPrlAtomicSort

  datatype 'i redprl_value =
     LCF of 'i NominalLcfV.t
   | LVL_V of 'i LevelV.t
   | CTT_V of 'i CttV.t
   | RCD_V of 'i RecordV.t
   | ATM_V of 'i AtomV.t
   | REFINE of Sort.t
   | VEC_LIT of Sort.t * int
   | STR_LIT of string
   | OP_SOME of Sort.t
   | OP_NONE of Sort.t

  datatype 'i redprl_cont =
     EXTRACT of Sort.t
   | LVL_K of 'i LevelK.t
   | CTT_K of 'i CttK.t
   | RCD_K of 'i RecordK.t
   | ATM_K of 'i AtomK.t

  datatype 'i redprl_def =
     CTT_D of 'i CttD.t
   | RCD_D of 'i RecordD.t
end

structure RedPrlV : ABT_OPERATOR =
struct
  structure Ar = RedPrlAtomicArity

  open RedPrlOperators ArityNotation
  type 'i t = 'i redprl_value

  infix <> ->>

  val arity =
    fn LCF theta => NominalLcfV.arity theta
     | LVL_V theta => LevelV.arity theta
     | CTT_V theta => CttV.arity theta
     | RCD_V theta => RecordV.arity theta
     | ATM_V theta => AtomV.arity theta
     | REFINE tau =>
         [[] * [] <> SortData.EXP,
          [] * [] <> SortData.TAC,
          [] * [] <> SortData.OPT tau]
            ->> SortData.THM tau
     | VEC_LIT (tau, len) =>
         (List.tabulate (len, fn _ => [] * [] <> tau))
           ->> SortData.VEC tau
     | STR_LIT str =>
         [] ->> SortData.STR
     | OP_SOME tau =>
         [[] * [] <> tau]
           ->> SortData.OPT tau
     | OP_NONE tau =>
         [] ->> SortData.OPT tau

  val support =
    fn LCF theta => NominalLcfV.support theta
     | LVL_V theta => LevelV.support theta
     | CTT_V theta => CttV.support theta
     | RCD_V theta => RecordV.support theta
     | ATM_V theta => AtomV.support theta
     | REFINE _ => []
     | VEC_LIT (tau, len) => []
     | STR_LIT _ => []
     | OP_SOME _ => []
     | OP_NONE _ => []

  fun eq f =
    fn (LCF th1, LCF th2) => NominalLcfV.eq f (th1, th2)
     | (LVL_V th1, LVL_V th2) => LevelV.eq f (th1, th2)
     | (CTT_V th1, CTT_V th2) => CttV.eq f (th1, th2)
     | (RCD_V th1, RCD_V th2) => RecordV.eq f (th1, th2)
     | (ATM_V th1, ATM_V th2) => AtomV.eq f (th1, th2)
     | (REFINE sigma, REFINE tau) => sigma = tau
     | (VEC_LIT p1, VEC_LIT p2) => p1 = p2
     | (STR_LIT s1, STR_LIT s2) => s1 = s2
     | (OP_SOME sigma, OP_SOME tau) => sigma = tau
     | (OP_NONE sigma, OP_NONE tau) => sigma = tau
     | _ => false

  fun toString f =
    fn LCF theta => NominalLcfV.toString f theta
     | LVL_V theta => LevelV.toString f theta
     | CTT_V theta => CttV.toString f theta
     | RCD_V theta => RecordV.toString f theta
     | ATM_V theta => AtomV.toString f theta
     | REFINE tau => "refine{" ^ Sort.toString tau ^ "}"
     | VEC_LIT (tau, len) => "vec{" ^ Sort.toString tau ^ "}"
     | STR_LIT str => "\"" ^ str ^ "\""
     | OP_SOME tau => "some{" ^ Sort.toString tau ^ "}"
     | OP_NONE tau => "none{" ^ Sort.toString tau ^ "}"


  fun map f =
    fn LCF theta => LCF (NominalLcfV.map f theta)
     | LVL_V theta => LVL_V (LevelV.map f theta)
     | CTT_V theta => CTT_V (CttV.map f theta)
     | RCD_V theta => RCD_V (RecordV.map f theta)
     | ATM_V theta => ATM_V (AtomV.map f theta)
     | REFINE tau => REFINE tau
     | VEC_LIT (tau, len) => VEC_LIT (tau, len)
     | STR_LIT str => STR_LIT str
     | OP_SOME tau => OP_SOME tau
     | OP_NONE tau => OP_NONE tau
end

structure RedPrlK :
sig
   include ABT_OPERATOR
   val input : 'i t -> RedPrlAtomicSort.t
end =
struct
  structure Ar = RedPrlAtomicArity

  open RedPrlOperators ArityNotation
  type 'i t = 'i redprl_cont

  infix <> ->>

  val arity =
    fn EXTRACT tau => [] ->> tau
     | LVL_K th => LevelK.arity th
     | CTT_K th => CttK.arity th
     | RCD_K th => RecordK.arity th
     | ATM_K th => AtomK.arity th

  val input =
    fn EXTRACT tau => SortData.THM tau
     | LVL_K th => LevelK.input th
     | CTT_K th => CttK.input th
     | RCD_K th => RecordK.input th
     | ATM_K th => AtomK.input th

  val support =
    fn EXTRACT tau => []
     | LVL_K th => LevelK.support th
     | CTT_K th => CttK.support th
     | RCD_K th => RecordK.support th
     | ATM_K th => AtomK.support th

  fun eq f =
    fn (EXTRACT sigma, EXTRACT tau) => sigma = tau
     | (LVL_K th1, LVL_K th2) => LevelK.eq f (th1, th2)
     | (CTT_K th1, CTT_K th2) => CttK.eq f (th1, th2)
     | (RCD_K th1, RCD_K th2) => RecordK.eq f (th1, th2)
     | (ATM_K th1, ATM_K th2) => AtomK.eq f (th1, th2)
     | _ => false

  fun toString f =
    fn EXTRACT tau => "extract"
     | LVL_K th => LevelK.toString f th
     | CTT_K th => CttK.toString f th
     | RCD_K th => RecordK.toString f th
     | ATM_K th => AtomK.toString f th

  fun map f =
    fn EXTRACT tau => EXTRACT tau
     | LVL_K th => LVL_K (LevelK.map f th)
     | CTT_K th => CTT_K (CttK.map f th)
     | RCD_K th => RCD_K (RecordK.map f th)
     | ATM_K th => ATM_K (AtomK.map f th)
end

structure RedPrlD : ABT_OPERATOR =
struct
  structure Ar = RedPrlAtomicArity

  open RedPrlOperators ArityNotation
  type 'i t = 'i redprl_def

  val arity =
    fn CTT_D th => CttD.arity th
     | RCD_D th => RecordD.arity th

  val support =
    fn CTT_D th => CttD.support th
     | RCD_D th => RecordD.support th

  fun eq f =
    fn (CTT_D th1, CTT_D th2) => CttD.eq f (th1, th2)
     | (RCD_D th1, RCD_D th2) => RecordD.eq f (th1, th2)
     | _ => false

  fun toString f =
    fn CTT_D th => CttD.toString f th
     | RCD_D th => RecordD.toString f th

  fun map f =
    fn CTT_D th => CTT_D (CttD.map f th)
     | RCD_D th => RCD_D (RecordD.map f th)
end
