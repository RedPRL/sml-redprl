structure Sequent : SEQUENT =
struct
  type prop = Abt.abt
  type context = (prop * Abt.sort) SymbolTelescope.telescope

  datatype sequent = >> of context * prop
  infix >>

  fun toString (H >> P) =
    SymbolTelescope.toString (fn (m, tau) => DebugShowAbt.toString m) H
      ^ " >> "
      ^ DebugShowAbt.toString P
end
