signature QUANTIFIER_KIT =
sig

  type quantifier_destruct = RedPrlAbt.abt -> RedPrlAbt.abt * RedPrlAbt.variable * RedPrlAbt.abt

  (* Standard type-equality rule for quantifiers, like Pi, Sigma, Ensemble,
   * Isect, etc. *)
  val TypeEq
    : quantifier_destruct
    -> RefinerKit.ntactic

  val IsType
    : quantifier_destruct
    -> RefinerKit.ntactic
end
