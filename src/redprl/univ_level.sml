structure RedPrlLevel :> REDPRL_LEVEL =
struct
  structure E = RedPrlError
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  structure Ctx = Sym.Ctx
  structure TP = TermPrinter

  (* normal form: minimum distance from zero and other variables *)
  type level = IntInf.int * IntInf.int Ctx.dict
  type t = level

  fun <= ((gap0, gapmap0), (gap1, gapmap1)) =
    IntInf.<= (gap0, gap1) andalso
    List.all
      (fn (var, g0) =>
        case Ctx.find gapmap1 var of
          SOME g1 => IntInf.<= (g0, g1)
        | NONE => false)
      (Ctx.toList gapmap0)

  (* smart constructors *)
  fun const i = (i, Ctx.empty)
  val zero = const 0
  fun above ((gap, gapmap), i) =
    let
      fun shift x = x + i
    in
      (shift gap, Ctx.map shift gapmap)
    end
  fun max ls =
    let
      fun f ((gap0, gapmap0), (gap1, gapmap1)) =
        (IntInf.max (gap0, gap1),
         Ctx.union gapmap0 gapmap1 (fn (_, g0, g1) => IntInf.max (g0, g1)))
    in
      List.foldl f zero ls
    end

  (* pretty printer *)

  (* TODO
   *   `pretty.sml` should adopt the following algorithm so that `pretty`
   *   is just `ppParam o toParam`. *)
  fun prettyVarGap (x, i) =
    if i = 0 then
      TP.ppSym x
    else if i = 1 then
      Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "labove", TP.ppSym x]))
    else
      Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "labove", TP.ppSym x, TP.ppIntInf i]))
  fun pretty (gap, gapmap) =
    let
      val varGaps = List.map prettyVarGap (Ctx.toList gapmap)
      val args = if gap = 0 then varGaps else TP.ppIntInf gap :: varGaps
    in
      if List.null args then TP.ppIntInf 0
      else Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep (Fpp.text "lmax" :: args)))
    end

  (* parser and generator *)
  type param = Sym.t P.term
  val rec fromParam =
    fn P.VAR x => (0, Ctx.singleton x 0)
     | P.APP (P.LCONST i) => const i
     | P.APP (P.LABOVE (l, i)) => above (fromParam l, i)
     | P.APP (P.LMAX ls) => max (List.map fromParam ls)
     | p => E.raiseError (E.INVALID_LEVEL (TP.ppParam p))

  fun constToParam i = P.APP (P.LCONST i)
  fun varGapToParam (x, i) =
    if i = 0 then P.VAR x
    else P.APP (P.LABOVE (P.VAR x, i))
  fun toParam (gap, gapmap) =
    let
      val varGapList = List.map varGapToParam (Ctx.toList gapmap)
      val args = if gap = 0 then varGapList else constToParam gap :: varGapList
    in
      if List.null args then constToParam 0 else P.APP (P.LMAX args)
    end
end
