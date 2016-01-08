structure LevelOperator : OPERATOR =
struct
  open LevelOperatorData SortData

  structure Arity = Arity

  type 'i t = 'i level_operator

  fun arity (LBASE i) = ([], LVL)
    | arity LSUCC = ([(([], []), LVL)], LVL)

  fun support (LBASE i) = [(i, LVL)]
    | support LSUCC = []

  structure Presheaf =
  struct
    type 'i t = 'i t
    fun map f (LBASE i) = LBASE (f i)
      | map f LSUCC = LSUCC
  end

  structure Eq =
  struct
    type 'i t = 'i t

    fun eq f (LBASE i, LBASE j) = f (i, j)
      | eq f (LSUCC, LSUCC) = true
      | eq _ _ = false
  end

  structure Show =
  struct
    type 'i t = 'i t
    fun toString f (LBASE i) = "lbase[" ^ f i ^ "]"
      | toString f LSUCC = "lsucc"
  end

end
