structure SortData =
struct
  datatype sort =
      EXP (* expressions *)
    | TRIV (* triviality *)
    | TAC (* tactics *)
    | MTAC (* multitactics *)
    | THM  of sort (* theorems *)
    | LVL (* levels *)
    | VEC of sort (* vector *)
    | OPT of sort (* optional *)
    | OPID (* operator ids *)
    | STR (* strings *)
end
