structure SortData =
struct
  datatype sort =
      EXP (* constructions *)
    | TAC (* tactics *)
    | MTAC (* multitactics *)
    | THM  of sort (* theorems *)
    | LVL (* levels *)
    | VEC of sort (* vector *)
    | OPT of sort (* optional *)
    | OPID (* operator ids *)
    | STR (* strings *)
    | RCD_LBL (* record labels *)
    | UNIT (* the unit sort *)
    | EXN (* exception names *)
end

structure RedPrlAtomicSort :> ABT_SORT where type t = SortData.sort =
struct
  open SortData
  type t = sort

  val eq : t * t -> bool = op=

  val rec toString =
    fn EXP => "exp"
     | TAC => "tac"
     | MTAC => "mtac"
     | THM tau => "thm{" ^ toString tau ^ "}"
     | LVL => "lvl"
     | VEC tau => "[" ^ toString tau ^ "]"
     | OPT tau => toString tau ^ "?"
     | OPID => "opid"
     | STR => "str"
     | RCD_LBL => "lbl"
     | UNIT => "unit"
     | EXN => "exn"
end

structure RedPrlAtomicSortJson =
struct
  local
    structure J = Json
    open SortData
  in
    val rec encode =
      fn EXP => J.String "exp"
       | TAC => J.String "tac"
       | MTAC => J.String "mtac"
       | LVL => J.String "lvl"
       | OPID => J.String "opid"
       | STR => J.String "str"
       | RCD_LBL => J.String "lbl"
       | UNIT => J.String "unit"
       | EXN => J.String "exn"
       | THM tau => J.Obj [("thm", encode tau)]
       | VEC tau => J.Obj [("vec", encode tau)]
       | OPT tau => J.Obj [("opt", encode tau)]

    val rec decode =
      fn J.String "exp" => SOME EXP
       | J.String "tac" => SOME TAC
       | J.String "mtac" => SOME MTAC
       | J.String "lvl" => SOME LVL
       | J.String "opid" => SOME OPID
       | J.String "str" => SOME STR
       | J.String "lbl" => SOME RCD_LBL
       | J.String "unit" => SOME UNIT
       | J.String "exn" => SOME EXN
       | J.Obj [("thm", tau)] => Option.map THM (decode tau)
       | J.Obj [("vec", tau)] => Option.map THM (decode tau)
       | J.Obj [("opt", tau)] => Option.map OPT (decode tau)
       | _ => NONE
  end
end
