structure RedPrlLevel =
struct
  open RedPrlParamData
  structure D = Sym.Ctx

  structure Normalization =
  struct
    (* normal form: minimum distance from zero and other variables *)
    type nf = IntInf.int * IntInf.int D.dict

    fun normalize f : 'a param_operator -> nf =
      fn LZERO => (0, D.empty)
       | LSUCC l =>
           let
             val (dist, distmap) : nf = f l
             fun succ d = dist + 1
           in
             (succ dist, D.map succ distmap)
           end
       | LMAX (l0, l1) =>
           let
             val (dist0, distmap0) = f l0
             val (dist1, distmap1) = f l1
             val merge = IntInf.max
           in
             (merge (dist0, dist1),
              D.union distmap0 distmap1 (fn (_, d0, d1) => merge (d0, d1)))
           end

    fun leq ((dist0, distmap0) : nf, (dist1, distmap1)) =
      dist0 <= dist1 andalso
      List.all
        (fn (var, d0) =>
          case D.find distmap1 var of
            SOME d1 => d0 <= d1
          | NONE => false)
        (D.toList distmap0)
  end
end
