signature QUANTIFIER_KIT =
sig
  (* Standard type-equality rule for quantifiers, like Pi, Sigma, Ensemble,
   * Isect, etc. *)
  val TypeEq
    : unit Abt.Operator.t
    -> RefinerKit.ntactic

  val destQuantifier
    : unit Abt.Operator.t
    -> Abt.abt
    -> Abt.abt * Abt.variable * Abt.abt
end

