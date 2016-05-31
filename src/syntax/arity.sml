structure RedPrlAtomicSort :> ABT_SORT where type t = SortData.sort =
struct
  open SortData
  type t = sort

  val eq = op=

  val rec toString =
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | (THM tau) => "thm{" ^ toString tau ^ "}"
     | LVL => "lvl"
     | (VEC tau) => "[" ^ toString tau ^ "]"
     | (OPT tau) => toString tau ^ "?"
     | OPID => "opid"
     | STR => "str"
     | RCD_LBL => "lbl"
end

structure ArityNotation =
struct
  fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
  fun op<> (a, b) = (a, b) (* valence *)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure RedPrlAtomicValence = AbtValence (structure S = RedPrlAtomicSort and Sp = ListSpine)
structure RedPrlAtomicArity = AbtArity (RedPrlAtomicValence)
