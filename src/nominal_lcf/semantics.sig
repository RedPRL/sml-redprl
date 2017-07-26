(* We extend a model of Nominal LCF to interpret tactics and multitactics. *)
signature NOMINAL_LCF_SEMANTICS =
sig
  include NOMINAL_LCF_MODEL

  (* [Σ |=[ρ] tac ==> T] *)
  val tactic : Syn.sign * env -> Syn.tactic -> tactic

  (* [Σ |=[ρ] mtac ==> M] *)
  val multitactic : Syn.sign * env -> Syn.multitactic -> multitactic
end
