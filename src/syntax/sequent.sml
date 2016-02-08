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

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort

  (* The meaning of the sequent with respect to its context of metavariables is
   * essentially the following: If the metavariables are replaced by closed abstractions
   * that respect computation, then the sequent is evident. *)
  datatype sequent = >> of context * concl
  infix >>

  val conclToString =
    fn TRUE (P, tau) => DebugShowAbt.toString P ^ " true"
     | TYPE (P, tau) => DebugShowAbt.toString P ^ " type"

  fun toString (H >> concl) =
    SymbolTelescope.toString (fn (m, tau) => DebugShowAbt.toString m) (#hypctx H)
      ^ " >> "
      ^ conclToString concl
end
