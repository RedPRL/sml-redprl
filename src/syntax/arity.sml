structure Sort :> SORT where type t = SortData.sort =
struct
  open SortData
  type t = sort

  structure Eq =
  struct
    type t = t
    val eq = op=
  end

  structure Show =
  struct
    type t = t
    fun toString EXP = "exp"
      | toString EVD = "evd"
      | toString TAC = "tac"
      | toString (VEC tau) = "[" ^ toString tau ^ "]"
      | toString (OPT tau) = toString tau ^ "?"
  end
end

structure Arity = Arity (structure Sort = Sort and Spine = ListSpine)
structure Valence = Arity.Valence
