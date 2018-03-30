structure RedPrlSort :> REDPRL_SORT = 
struct
  datatype sort = datatype SortData.sort
  type t = sort

  val eq : t * t -> bool = 
    op=

  val rec toString = 
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | JDG => "jdg"
     | MATCH_CLAUSE => "match-clause"
     | DIM => "dim"
     | TUBE tau => "tube{" ^ toString tau ^ "}"
     | BDRY tau => "bdry{" ^ toString tau ^ "}"
     | VEC tau => "vec{" ^ toString tau ^ "}"
     | LVL => "lvl"
     | KND => "knd"
     | SEL => "sel"
     | ACC => "acc"
     | ANY => "any"
     | META_NAME => "meta-name"
     | IND_SPECTYPE => "ind-spectype"
     | IND_SPEC => "ind-spec"
     | IND_FAM => "ind-fam"
     | IND_CONSTR => "ind-constr"
end

structure RedPrlArity = ListAbtArity (structure S = RedPrlSort)
