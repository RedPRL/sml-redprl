(* This is the sum type containing all the operators in JonPRL's
 * programming language. *)
structure OperatorData =
struct
  datatype 'i operator =
      LCF of 'i NominalLcfOperator.t
    | PROVE
    | LVL_OP of 'i LevelOperator.t
    | CTT of 'i CttOperator.t
    | VEC_LIT of Sort.t * int
    | STR_LIT of string
    | OP_SOME of Sort.t
    | OP_NONE of Sort.t
    | CUST of 'i * ('i * Sort.t) list * Arity.t
end

