structure RedPrlLevel =
struct
  structure E = RedPrlError
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  structure Ctx = Sym.Ctx
  structure TP = TermPrinter

  type param = Sym.t P.term

  structure Normalization =
  struct
    (* normal form: minimum distance from zero and other variables *)
    type nf = IntInf.int * IntInf.int Ctx.dict

    val rec normalize : param -> nf =
      fn P.VAR x => (0, Ctx.singleton x 0)
       | P.APP P.LZERO => (0, Ctx.empty)
       | P.APP (P.LSUCC lvl) =>
           let
             val (dist, distmap) : nf = normalize lvl
             fun succ d = dist + 1
           in
             (succ dist, Ctx.map succ distmap)
           end
       | P.APP (P.LMAX (lvl0, lvl1)) =>
           let
             val (dist0, distmap0) = normalize lvl0
             val (dist1, distmap1) = normalize lvl1
             val max = IntInf.max
           in
             (max (dist0, dist1),
              Ctx.union distmap0 distmap1 (fn (_, d0, d1) => max (d0, d1)))
           end
       | p => E.raiseError (E.INVALID_LEVEL (TP.ppParam p))

    fun leq ((dist0, distmap0) : nf, (dist1, distmap1)) =
      dist0 <= dist1 andalso
      List.all
        (fn (var, d0) =>
          case Ctx.find distmap1 var of
            SOME d1 => d0 <= d1
          | NONE => false)
        (Ctx.toList distmap0)
  end

  structure N = Normalization

  fun leq (param0, param1) =
    N.leq (N.normalize param0, N.normalize param1)
end
