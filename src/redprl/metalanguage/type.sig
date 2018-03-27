structure MlTypeData =
struct
  type sort = RedPrlSort.t
  type valence = RedPrlArity.valence

  datatype vty =
     ONE
   | DOWN of cty
   | TERM of sort
   | THM of sort
   | ABS of valence list * vty
   | METAS of valence list
   | DATA_INFO of InductiveSpec.precomputedArity
   (* TODO:
   | SUM of (string * vty) list
   *)

  and cty =
     UP of vty
   | FUN of vty * cty
   (* TODO:
   | RECORD of (string * cty) list
   *)
end

signature ML_TYPE =
sig
  datatype vty = datatype MlTypeData.vty
  datatype cty = datatype MlTypeData.cty

  val eqVty : vty * vty -> bool
  val eqCty : cty * cty -> bool

  (* TODO:

  val ppVty : vty -> Fpp.doc
  val ppCty : cty -> Fpp.doc

  *)
end
