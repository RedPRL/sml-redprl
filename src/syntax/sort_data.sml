structure SortData =
struct
  datatype sort =
      EXP (* expressions *)
    | EVD (* derivations *)
    | TAC (* tactics *)
    | LVL (* levels *)
    | VEC of sort (* vector *)
    | OPT of sort (* optional *)
end
