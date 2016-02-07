structure Sequent : SEQUENT =
struct
  type prop = Abt.abt
  type sort = Abt.sort

  type context =
    {metactx : Abt.metactx,
     symctx : Abt.symctx,
     hypctx : (prop * sort) SymbolTelescope.telescope}

  (* A sequent consists in a context (of metavariables, symbols and hypotheses)
   * and a conclusion [(P,tau)], where [tau] is the sort of the evidence to be
   * produced, and [P] is a type that refines [tau] which shall classify the
   * evidence. *)
  datatype sequent = >> of context * (prop * sort)
  infix >>

  fun toString (H >> (P, tau)) =
    SymbolTelescope.toString (fn (m, tau) => DebugShowAbt.toString m) (#hypctx H)
      ^ " >> "
      ^ DebugShowAbt.toString P
end
