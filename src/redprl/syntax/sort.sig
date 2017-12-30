structure SortData = 
struct
  datatype sort =
     EXP
   | TAC
   | MTAC
   | JDG
   | TRV
   | MATCH_CLAUSE
   | DIM | TUBE | BDRY
   | VEC of sort
   | LVL
   | KND
   | SEL
   | ACC
   | ANY
   | META_NAME
end

signature REDPRL_SORT = 
sig
  datatype sort = datatype SortData.sort
  include ABT_SORT where type t = sort
end