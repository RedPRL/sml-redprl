structure Sequent : SEQUENT =
struct
  type prop = Abt.abt
  type sort = Abt.sort

  type context =
    {metactx : Abt.metactx,
     symctx : Abt.symctx,
     hypctx : (prop * sort) SymbolTelescope.telescope}

  datatype sequent = >> of context * (prop * sort)
  infix >>

  fun toString (H >> (P, tau)) =
    SymbolTelescope.toString (fn (m, tau) => DebugShowAbt.toString m) (#hypctx H)
      ^ " >> "
      ^ DebugShowAbt.toString P
end
