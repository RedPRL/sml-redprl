structure SortData =
struct
  datatype sort =
      EXP (* expressions *)
    | EVD (* derivations *)
    | TAC (* tactics *)
    | VEC of sort (* vector *)
    | OPT of sort (* optional *)
end
