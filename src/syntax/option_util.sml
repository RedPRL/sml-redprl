structure OptionUtil :> OPTION_UTIL =
struct
  fun traverseOpt f xs =
    SOME (List.map (Option.valOf o f) xs)
      handle _ => NONE

  fun ** (SOME a, SOME b) = SOME (a, b)
    | ** _ = NONE
end
