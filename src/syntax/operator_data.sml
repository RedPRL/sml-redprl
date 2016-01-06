(* This is the sum type containing all the operators in JonPRL's
 * programming language. *)
structure OperatorData =
struct
  datatype 'i operator =
      S of 'i ScriptOperator.t
    | VEC_LIT of Sort.t * int
end

