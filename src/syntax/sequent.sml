structure Sequent : SEQUENT =
struct
  type prop = Abt.abt
  type context = prop SymbolTelescope.telescope

  datatype sequent = >> of context * prop
  infix >>

  fun toString (H >> P) =
    SymbolTelescope.toString DebugShowAbt.toString H
      ^ " >> "
      ^ DebugShowAbt.toString P
end
