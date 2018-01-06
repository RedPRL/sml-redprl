(* The semantic domain for metalanguage programs. *)
signature ML_SEMANTICS = 
sig
  type env
  type syn_cmd
  type jdg = AtomicJudgment.jdg
  type term = Tm.abt
  type metas = (Tm.metavariable * Tm.valence) list

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
  val lookupMeta : env -> Tm.metavariable -> Tm.metavariable
  val term : env -> term -> term

  val extend : env -> MlId.t -> value -> env
  val renameEnv : env -> Tm.metavariable Tm.Metavar.Ctx.dict -> env
  val renameVal : value -> Tm.metavariable Tm.Metavar.Ctx.dict -> value

  val ppValue : value -> Fpp.doc

  (* TODO: move into evaluator *)
  val printVal : Pos.t option * value -> unit
end
