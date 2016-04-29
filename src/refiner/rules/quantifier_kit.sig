signature QUANTIFIER_KIT =
sig
  (* Standard type-equality rule for quantifiers, like Pi, Sigma, Ensemble,
   * Isect, etc. *)
  val TypeEq : unit Abt.Operator.t -> RefinerKit.ntactic
end

