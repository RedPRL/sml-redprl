(* The semantic domain for metalanguage programs. *)
signature ML_SEMANTICS = 
sig
  type env
  type syn_cmd
  type jdg
  type term
  type metavariable
  type metas = (metavariable * Tm.valence) list

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
  val lookupMeta : env -> metavariable -> metavariable  
  val term : env -> term -> term

  val extend : env -> MlId.t -> value -> env
  val rename : env -> metavariable list -> metavariable list -> env

  val ppValue : value -> Fpp.doc

  (* TODO: move into evaluator *)
  val printVal : Pos.t option * value -> unit
end
