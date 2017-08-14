structure RedPrlLevel :> REDPRL_LEVEL =
struct
  structure E = RedPrlError
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  structure Ctx = Sym.Ctx
  structure TP = TermPrinter

  (* normal form: minimum distance from zero and other variables *)
  type level = IntInf.int * IntInf.int Ctx.dict
  type t = level

  fun <= ((dist0, distmap0), (dist1, distmap1)) =
    IntInf.<= (dist0, dist1) andalso
    List.all
      (fn (var, d0) =>
        case Ctx.find distmap1 var of
          SOME d1 => IntInf.<= (d0, d1)
        | NONE => false)
      (Ctx.toList distmap0)

  fun succ (dist, distmap) =
    let
      fun succ i = IntInf.+ (i, 1)
    in
      (succ dist, Ctx.map succ distmap)
    end

  fun max ((dist0, distmap0), (dist1, distmap1)) =
    let
      val max = IntInf.max
    in
      (max (dist0, dist1),
       Ctx.union distmap0 distmap1 (fn (_, d0, d1) => max (d0, d1)))
    end

  type param = Sym.t P.term

  val rec fromParam =
    fn P.VAR x => (0, Ctx.singleton x 0)
     | P.APP P.LZERO => (0, Ctx.empty)
     | P.APP (P.LSUCC lvl) => succ (fromParam lvl)
     | P.APP (P.LMAX (lvl0, lvl1)) => max (fromParam lvl0, fromParam lvl1)
     | p => E.raiseError (E.INVALID_LEVEL (TP.ppParam p))

  fun gapToParam i p =
    case IntInf.compare (i, 0) of
      GREATER => P.APP (P.LSUCC (gapToParam (i - 1) p))
    | EQUAL => p
    | LESS => E.raiseError (E.INVALID_LEVEL (TP.ppIntInf i))

  fun constToParam i = gapToParam i (P.APP P.LZERO)

  fun varGapToParam i x = gapToParam i (P.VAR x)

  fun toParam (dist, distmap) =
    Ctx.foldr
      (fn (x, i, p) => P.APP (P.LMAX (varGapToParam i x, p)))
      (constToParam dist)
      distmap
end
