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

  and cty =
      UP of vty
end

signature ML_TYPE =
sig
  datatype vty = datatype MlTypeData.vty
  datatype cty = datatype MlTypeData.cty

  (* TODO: pretty printer *)
end
