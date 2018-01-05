(* The semantic domain for metalanguage programs. *)
signature ML_SEMANTICS = 
sig
  type env
  type syn_cmd
  type jdg
  type term
  type metas

  datatype value =
     THUNK of env * syn_cmd
   | THM of jdg * term
   | TERM of term
   | ABS of value * value
   | METAS of metas
   | NIL

  datatype cmd = 
     RET of value
   | FN of env * MlId.t * syn_cmd

  val initEnv : env
  val lookup : env -> MlId.t -> value
  val extend : env -> MlId.t -> value -> env
  val ppValue : value -> Fpp.doc

  val printVal : Pos.t option * value -> unit
end
