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
     | TRV => "trv"
     | MATCH_CLAUSE => "match-clause"
     | DIM => "dim"
     | TUBE => "tube"
     | BDRY => "bdry"
     | VEC tau => "vec{" ^ toString tau ^ "}"
     | LVL => "lvl"
     | KND => "knd"
     | SEL => "sel"
     | ACC => "acc"
     | ANY => "any"
     | META_NAME => "meta-name"
end

structure RedPrlArity = ListAbtArity (structure S = RedPrlSort)