structure LevelOperatorData =
struct
  datatype 'i level_operator =
      LBASE
    | LSUCC
end

structure LevelOperator : OPERATOR =
struct
  open LevelOperatorData SortData

  structure Arity = Arity

  type 'i t = 'i level_operator

  fun arity LBASE = ([], LVL)
    | arity LSUCC = ([(([], []), LVL)], LVL)

  fun support LBASE = []
    | support LSUCC = []

  fun map f LBASE = LBASE
    | map f LSUCC = LSUCC

  fun eq f (LBASE, LBASE) = true
    | eq f (LSUCC, LSUCC) = true
    | eq _ _ = false

  fun toString f LBASE = "lbase"
    | toString f LSUCC = "lsucc"

end
