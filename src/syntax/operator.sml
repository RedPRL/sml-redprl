(* This is the sum type containing all the operators in JonPRL's
 * programming language. *)
structure OperatorData =
struct
  datatype 'i operator =
      LCF of 'i NominalLcfOperator.t
    | REFINE of Sort.t
    | EXTRACT of Sort.t
    | LVL_OP of 'i LevelOperator.t
    | CTT of 'i CttOperator.t
    | RCD of 'i RecordOperator.t
    | ATM of 'i AtomsOperator.t
    | VEC_LIT of Sort.t * int
    | STR_LIT of string
    | OP_SOME of Sort.t
    | OP_NONE of Sort.t
    | CUST of 'i * ('i * Sort.t) list * Arity.t
end

structure Operator : ABT_OPERATOR =
struct
  open OperatorData
  structure Ar = Arity

  type 'i t = 'i operator

  local
    fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun op<> (a, b) = (a, b) (* valence *)
    fun op->> (a, b) = (a, b) (* arity *)
    fun op^ (x, n) = List.tabulate (n, fn _ => x)
    infix 5 <> ->>
    infix 6 * ^
  in
    fun arity theta =
      case theta of
           LCF theta =>
             NominalLcfOperator.arity theta
         | CTT theta =>
             CttOperator.arity theta
         | RCD theta =>
             RecordOperator.arity theta
         | ATM theta =>
             AtomsOperator.arity theta
         | REFINE tau =>
             [[] * [] <> SortData.EXP,
              [] * [] <> SortData.TAC,
              [] * [] <> SortData.OPT tau]
                ->> SortData.THM tau
         | EXTRACT tau =>
             [[] * [] <> SortData.THM tau]
                ->> tau
         | LVL_OP theta =>
             LevelOperator.arity theta
         | VEC_LIT (tau, len) =>
             ([] * [] <> tau) ^ len
               ->> SortData.VEC tau
         | STR_LIT str =>
             [] ->> SortData.STR
         | OP_SOME tau =>
             [[] * [] <> tau]
               ->> SortData.OPT tau
         | OP_NONE tau =>
             [] ->> SortData.OPT tau
         | CUST (_, _, arity) =>
             arity
  end

  fun support theta =
    case theta of
         LCF theta => NominalLcfOperator.support theta
       | CTT theta => CttOperator.support theta
       | RCD theta => RecordOperator.support theta
       | ATM theta => AtomsOperator.support theta
       | REFINE _ => []
       | EXTRACT _ => []
       | LVL_OP theta => LevelOperator.support theta
       | VEC_LIT (tau, len) => []
       | STR_LIT _ => []
       | OP_SOME _ => []
       | OP_NONE _ => []
       | CUST (opid, supp, _) => (opid, SortData.OPID) :: supp

  fun map f theta =
    case theta of
         LCF theta => LCF (NominalLcfOperator.map f theta)
       | CTT theta => CTT (CttOperator.map f theta)
       | RCD theta => RCD (RecordOperator.map f theta)
       | ATM theta => ATM (AtomsOperator.map f theta)
       | REFINE tau => REFINE tau
       | EXTRACT tau => EXTRACT tau
       | LVL_OP theta => LVL_OP (LevelOperator.map f theta)
       | VEC_LIT p => VEC_LIT p
       | STR_LIT p => STR_LIT p
       | OP_SOME tau => OP_SOME tau
       | OP_NONE tau => OP_NONE tau
       | CUST (opid, supp, arity) => CUST (f opid, List.map (fn (u, tau) => (f u, tau)) supp, arity)

  fun eq f ops =
    case ops of
         (LCF theta1, LCF theta2) =>
           NominalLcfOperator.eq f (theta1, theta2)
       | (CTT theta1, CTT theta2) =>
           CttOperator.eq f (theta1, theta2)
       | (RCD theta1, RCD theta2) =>
           RecordOperator.eq f (theta1, theta2)
       | (ATM theta1, ATM theta2) =>
           AtomsOperator.eq f (theta1, theta2)
       | (REFINE tau1, REFINE tau2) =>
           Sort.eq (tau1, tau2)
       | (EXTRACT tau1, EXTRACT tau2) =>
           Sort.eq (tau1, tau2)
       | (LVL_OP theta1, LVL_OP theta2) =>
           LevelOperator.eq f (theta1, theta2)
       | (VEC_LIT p1, VEC_LIT p2) =>
           p1 = p2
       | (STR_LIT p1, STR_LIT p2) =>
           p1 = p2
       | (OP_SOME tau1, OP_SOME tau2) =>
           tau1 = tau2
       | (OP_NONE tau1, OP_NONE tau2) =>
           tau1 = tau2
       | (CUST (opid1, supp1, arity1), CUST (opid2, supp2, arity2)) =>
           f (opid1, opid2)
             andalso ListPair.allEq (fn ((u, sigma), (v, tau)) => f (u, v) andalso Sort.eq (sigma, tau)) (supp1, supp2)
             andalso Arity.eq (arity1, arity2)
       | _ =>
           false

  fun toString f theta =
    case theta of
         LCF theta =>
           NominalLcfOperator.toString f theta
       | CTT theta =>
           CttOperator.toString f theta
       | RCD theta =>
           RecordOperator.toString f theta
       | ATM theta =>
           AtomsOperator.toString f theta
       | REFINE tau => "refine{" ^ Sort.toString tau ^ "}"
       | EXTRACT tau => "extract{" ^ Sort.toString tau ^ "}"
       | LVL_OP theta =>
           LevelOperator.toString f theta
       | VEC_LIT (tau, m) =>
           "vec{" ^ Sort.toString tau ^ "}"
       | STR_LIT str =>
           "\"" ^ str ^ "\""
       | OP_SOME tau =>
           "some{" ^ Sort.toString tau ^ "}"
       | OP_NONE tau =>
           "none{" ^ Sort.toString tau ^ "}"
       | CUST (opid, supp, _) =>
           let
             fun spine [] = ""
               | spine xs = "[" ^ ListSpine.pretty f "," xs ^ "]"
           in
             f opid ^ spine (List.map #1 supp)
           end
end
