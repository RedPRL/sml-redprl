structure LevelOperatorData =
struct
  datatype 'i level_operator =
      LBASE
    | LSUCC
    | LSUP
end

structure LevelOperator : OPERATOR =
struct
  open LevelOperatorData SortData

  structure Arity = Arity

  type 'i t = 'i level_operator

  fun arity LBASE = ([], LVL)
    | arity LSUCC = ([(([], []), LVL)], LVL)
    | arity LSUP = ([(([],[]), LVL), (([],[]), LVL)], LVL)

  fun support LBASE = []
    | support LSUCC = []
    | support LSUP = []

  fun map f LBASE = LBASE
    | map f LSUCC = LSUCC
    | map f LSUP = LSUP

  fun eq f (LBASE, LBASE) = true
    | eq f (LSUCC, LSUCC) = true
    | eq f (LSUP, LSUP) = true
    | eq _ _ = false

  fun toString f LBASE = "lbase"
    | toString f LSUCC = "lsucc"
    | toString f LSUP = "lsup"

end
