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
   | CUB_V of 'i CubicalV.t
   | REFINE of Sort.t
   | VEC_LIT of Sort.t * int
   | STR_LIT of string
   | OP_SOME of Sort.t
   | OP_NONE of Sort.t
   | EXN of 'i

  datatype 'i redprl_cont =
     EXTRACT of Sort.t
   | FROM_SOME of Sort.t
   | LVL_K of 'i LevelK.t
   | CTT_K of 'i CttK.t
   | RCD_K of 'i RecordK.t
   | ATM_K of 'i AtomK.t
   | CUB_K of 'i CubicalK.t
   | THROW
   | CATCH of 'i

  datatype 'i redprl_def =
     CTT_D of 'i CttD.t
   | RCD_D of 'i RecordD.t
   | CUB_D of 'i CubicalK.t
end

structure RedPrlV : JSON_ABT_OPERATOR =
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
     | EXN _ =>
         [[] * [] <> SortData.EXP] ->> SortData.EXP

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
     | EXN i => [(i, SortData.EXN)]

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
     | (EXN a, EXN b) => f (a, b)
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
     | EXN a => "exn[" ^ f a ^ "]"


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
     | EXN a => EXN (f a)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn LCF theta => J.Obj [("lcf", NominalLcfV.encode f theta)]
     | LVL_V theta => J.Obj [("lvl", LevelV.encode f theta)]
     | CTT_V theta => J.Obj [("ctt", CttV.encode f theta)]
     | RCD_V theta => J.Obj [("rcd", RecordV.encode f theta)]
     | ATM_V theta => J.Obj [("atm", AtomV.encode f theta)]
     | REFINE tau => J.Obj [("refine", S.encode tau)]
     | VEC_LIT (tau, len) => J.Obj [("vec", J.Array [S.encode tau, J.Int len])]
     | STR_LIT str => J.Obj [("str", J.String str)]
     | OP_SOME tau => J.Obj [("some", S.encode tau)]
     | OP_NONE tau => J.Obj [("none", S.encode tau)]
     | EXN a => J.Obj [("exn", f a)]

  fun decode f =
    fn J.Obj [("lcf", theta)] => Option.map LCF (NominalLcfV.decode f theta)
     | J.Obj [("lvl", theta)] => Option.map LVL_V (LevelV.decode f theta)
     | J.Obj [("ctt", theta)] => Option.map CTT_V (CttV.decode f theta)
     | J.Obj [("rcd", theta)] => Option.map RCD_V (RecordV.decode f theta)
     | J.Obj [("atm", theta)] => Option.map ATM_V (AtomV.decode f theta)
     | J.Obj [("refine", tau)] => Option.map REFINE (S.decode tau)
     | J.Obj [("vec", J.Array [tau, J.Int len])] => Option.map (fn tau' => VEC_LIT (tau', len)) (S.decode tau)
     | J.Obj [("str", J.String str)] => SOME (STR_LIT str)
     | J.Obj [("some", tau)] => Option.map OP_SOME (S.decode tau)
     | J.Obj [("none", tau)] => Option.map OP_NONE (S.decode tau)
     | J.Obj [("exn", a)] => Option.map EXN (f a)
     | _ => NONE
end

structure RedPrlK :
sig
   include JSON_ABT_OPERATOR
   val input : 'i t -> RedPrlAtomicSort.t list * RedPrlAtomicSort.t
end =
struct
  structure Ar = RedPrlAtomicArity

  open RedPrlOperators ArityNotation
  type 'i t = 'i redprl_cont

  infix 9 <> ->>

  val arity =
    fn EXTRACT tau => [] ->> tau
     | FROM_SOME tau => [] ->> tau
     | LVL_K th => LevelK.arity th
     | CTT_K th => CttK.arity th
     | RCD_K th => RecordK.arity th
     | ATM_K th => AtomK.arity th
     | THROW => [] ->> SortData.EXP
     | CATCH a => [[] <> [SortData.EXP] * SortData.EXP] ->> SortData.EXP

  val input =
    fn EXTRACT tau => ([], SortData.THM tau)
     | FROM_SOME tau => ([], SortData.OPT tau)
     | LVL_K th => LevelK.input th
     | CTT_K th => CttK.input th
     | RCD_K th => RecordK.input th
     | ATM_K th => AtomK.input th
     | THROW => ([], SortData.EXP)
     | CATCH _ => ([], SortData.EXP)

  val support =
    fn EXTRACT tau => []
     | FROM_SOME tau => []
     | LVL_K th => LevelK.support th
     | CTT_K th => CttK.support th
     | RCD_K th => RecordK.support th
     | ATM_K th => AtomK.support th
     | THROW => []
     | CATCH a => [(a, SortData.EXN)]

  fun eq f =
    fn (EXTRACT sigma, EXTRACT tau) => sigma = tau
     | (FROM_SOME sigma, FROM_SOME tau) => sigma = tau
     | (LVL_K th1, LVL_K th2) => LevelK.eq f (th1, th2)
     | (CTT_K th1, CTT_K th2) => CttK.eq f (th1, th2)
     | (RCD_K th1, RCD_K th2) => RecordK.eq f (th1, th2)
     | (ATM_K th1, ATM_K th2) => AtomK.eq f (th1, th2)
     | (THROW, THROW) => true
     | (CATCH a, CATCH b) => f (a, b)
     | _ => false

  fun toString f =
    fn EXTRACT tau => "extract"
     | FROM_SOME tau => "extract1"
     | LVL_K th => LevelK.toString f th
     | CTT_K th => CttK.toString f th
     | RCD_K th => RecordK.toString f th
     | ATM_K th => AtomK.toString f th
     | THROW => "throw"
     | CATCH a => "catch[" ^ f a ^ "]"

  fun map f =
    fn EXTRACT tau => EXTRACT tau
     | FROM_SOME tau => FROM_SOME tau
     | LVL_K th => LVL_K (LevelK.map f th)
     | CTT_K th => CTT_K (CttK.map f th)
     | RCD_K th => RCD_K (RecordK.map f th)
     | ATM_K th => ATM_K (AtomK.map f th)
     | THROW => THROW
     | CATCH a => CATCH (f a)

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn EXTRACT tau => J.Obj [("extract", S.encode tau)]
     | FROM_SOME tau => J.Obj [("from_some", S.encode tau)]
     | LVL_K th => J.Obj [("lvl", LevelK.encode f th)]
     | CTT_K th => J.Obj [("ctt", CttK.encode f th)]
     | RCD_K th => J.Obj [("rcd", RecordK.encode f th)]
     | ATM_K th => J.Obj [("atm", AtomK.encode f th)]
     | THROW => J.String "throw"
     | CATCH a => J.Obj [("catch", f a)]

  fun decode f =
    fn J.Obj [("extract", tau)] => Option.map EXTRACT (S.decode tau)
     | J.Obj [("from_some", tau)] => Option.map FROM_SOME (S.decode tau)
     | J.Obj [("lvl", th)] => Option.map LVL_K (LevelK.decode f th)
     | J.Obj [("ctt", th)] => Option.map CTT_K (CttK.decode f th)
     | J.Obj [("rcd", th)] => Option.map RCD_K (RecordK.decode f th)
     | J.Obj [("atm", th)] => Option.map ATM_K (AtomK.decode f th)
     | J.String "throw" => SOME THROW
     | J.Obj [("catch", a)] => Option.map CATCH (f a)
     | _ => NONE
end

structure RedPrlD : JSON_ABT_OPERATOR =
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

  structure J = Json and S = RedPrlAtomicSortJson

  fun encode f =
    fn CTT_D th => J.Obj [("ctt", CttD.encode f th)]
     | RCD_D th => J.Obj [("rcd", RecordD.encode f th)]

  fun decode f =
    fn J.Obj [("ctt", th)] => Option.map CTT_D (CttD.decode f th)
     | J.Obj [("rcd", th)] => Option.map RCD_D (RecordD.decode f th)
     | _ => NONE
end
