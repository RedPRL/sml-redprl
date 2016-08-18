structure RedPrlExn =
struct
  exception RedPrlExn of Pos.t option * string

  val rec toString =
    fn RedPrlExn (SOME pos, msg) => Pos.toString pos ^ ": " ^ msg
     | RedPrlExn (NONE, msg) => msg
     | Fail msg => msg
     | exn => exnMessage exn

  fun wrap pos =
    fn RedPrlExn (_, msg) => RedPrlExn (pos, msg)
     | exn => RedPrlExn (pos, toString exn)
end
