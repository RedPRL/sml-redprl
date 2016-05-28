signature QUANTIFIER_KIT =
sig
  (* Standard type-equality rule for quantifiers, like Pi, Sigma, Ensemble,
   * Isect, etc. *)
  val TypeEq
    : unit Abt.O.t
    -> RefinerKit.ntactic

  val IsType
    : unit Abt.O.t
    -> RefinerKit.ntactic

  val destQuantifier
    : unit Abt.O.t
    -> Abt.abt
    -> Abt.abt * Abt.variable * Abt.abt
end

