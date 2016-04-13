(* A model of Nominal LCF consists in a tactic metalanguage, and an interpretation
 * of primitive tactics into this language. *)
signature NOMINAL_LCF_MODEL =
sig
  structure Syn : NOMINAL_LCF_SYNTAX
  structure Lcf : DEPENDENT_LCF

  type 'a seq = int -> 'a

  type tactic = Syn.symbol seq -> Lcf.tactic
  type multitactic = Syn.symbol seq -> Lcf.multitactic

  (* signature *)
  type env = tactic Syn.VarCtx.dict

  type ('syn, 'sem) interp = Syn.sign * env -> 'syn -> 'sem

  val tacticR : (Syn.statement, tactic) interp -> (Syn.tactic, tactic) interp
end

(* We extend a model of Nominal LCF to interpret multitactics and statements. *)
signature NOMINAL_LCF_SEMANTICS =
sig
  include NOMINAL_LCF_MODEL

  val tactic : (Syn.tactic, tactic) interp
  val multitactic : (Syn.multitactic, multitactic) interp
  val statement : (Syn.statement, tactic) interp
end
