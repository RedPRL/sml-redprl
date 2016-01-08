(* This is the sum type containing all the operators in JonPRL's
 * programming language. *)
structure OperatorData =
struct
  datatype 'i operator =
      S of 'i ScriptOperator.t
    | LVL_OP of 'i LevelOperator.t
    | VEC_LIT of Sort.t * int
    | OP_SOME of Sort.t
    | OP_NONE of Sort.t
end

