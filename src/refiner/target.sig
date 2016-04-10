signature TARGET =
sig
  type symbol
  type judgment
  type abt

  datatype target =
      TARGET_HYP of symbol
    | TARGET_CONCL

  val targetRewrite
    : (abt -> abt)
    -> target
    -> judgment
    -> judgment
end
