structure Sort :> SORT where type t = SortData.sort =
struct
  open SortData
  type t = sort

  val eq = op=

  val rec toString =
    fn EXP => "exp"
     | EVD => "evd"
     | TAC => "tac"
     | MTAC => "mtac"
     | THM => "thm"
     | LVL => "lvl"
     | (VEC tau) => "[" ^ toString tau ^ "]"
     | (OPT tau) => toString tau ^ "?"
     | OPID => "opid"
     | STR => "str"
end

structure Valence = Valence (structure Sort = Sort and Spine = ListSpine)
structure Arity = Arity (Valence)
