functor RedPrlLevelPure (Key : ORDERED)
=
struct
  structure E = RedPrlError
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  structure D = SplayDict (structure Key = Key)
  structure TP = TermPrinter

  (* normal form: minimum distance from zero and other variables *)
  type level = IntInf.int * IntInf.int D.dict
  type t = level

  (* smart constructors *)
  fun const i = (i, D.empty)
  val zero = const 0 : level
  fun above ((gap, gapmap) : level, i) =
    let
      fun shift x = x + i
    in
      (shift gap, D.map shift gapmap)
    end
  fun max ls =
    let
      fun f ((gap0, gapmap0), (gap1, gapmap1)) =
        (IntInf.max (gap0, gap1),
         D.union gapmap0 gapmap1 (fn (_, g0, g1) => IntInf.max (g0, g1)))
    in
      List.foldl f zero ls
    end

  fun op <= ((gap0, gapmap0), (gap1, gapmap1)) =
    IntInf.<= (gap0, gap1) andalso
    List.all
      (fn (var, g0) =>
        case D.find gapmap1 var of
          SOME g1 => IntInf.<= (g0, g1)
        | NONE => false)
      (D.toList gapmap0)
  fun eq ((gap0, gapmap0) : level, (gap1, gapmap1) : level)
    = gap0 = gap1 andalso
      ListPair.allEq
        (fn ((v0, g0), (v1, g1)) => Key.eq (v0, v1) andalso g0 = g1)
        (D.toList gapmap0, D.toList gapmap1)
  fun isZero ((gap, gapmap) : level) = gap = 0 andalso D.isEmpty gapmap

  (* pretty printer *)
  type sym = Key.t

  (* TODO
   *   `pretty.sml` should adopt the following algorithm so that `pretty`
   *   is just `ppParam o toParam`. *)
  fun prettyVarGap (f : sym -> Fpp.doc) (x, i) =
    if i = 0 then
      f x
    else if i = 1 then
      Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "labove", f x]))
    else
      Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep
        [Fpp.text "labove", f x, TP.ppIntInf i]))
  fun pretty' f (gap, gapmap) =
    let
      val varGaps = List.map (prettyVarGap f) (D.toList gapmap)
      val args = if gap = 0 then varGaps else TP.ppIntInf gap :: varGaps
    in
      if List.null args then TP.ppIntInf 0
      else Fpp.Atomic.braces (Fpp.expr (Fpp.hvsep (Fpp.text "lmax" :: args)))
    end

  (* parser and generator *)
  type param = Key.t P.term
  fun out' (f : param -> Fpp.doc) : param -> level =
    fn P.VAR x => (0, D.singleton x 0)
     | P.APP (P.LCONST i) => const i
     | P.APP (P.LABOVE (l, i)) => above (out' f l, i)
     | P.APP (P.LMAX ls) => max (List.map (out' f) ls)
     | p => E.raiseError (E.INVALID_LEVEL (f p))

  fun constToParam i = P.APP (P.LCONST i)
  fun varGapToParam (x, i) =
    if i = 0 then P.VAR x
    else P.APP (P.LABOVE (P.VAR x, i))
  fun into (gap, gapmap) =
    let
      val varGapList = List.map varGapToParam (D.toList gapmap)
      val args = if gap = 0 then varGapList else constToParam gap :: varGapList
    in
      if List.null args then constToParam 0 else P.APP (P.LMAX args)
    end
end

structure RedPrlAbtLevel :> REDPRL_LEVEL =
struct
  local
    structure L = RedPrlLevelPure (Sym.Ord)
  in
    open L
    val pretty = pretty' TP.ppSym
    val out = out' TP.ppParam
  end
end
structure RedPrlAstLevel :> REDPRL_LEVEL =
struct
  local
    structure L = RedPrlLevelPure (StringOrdered)
  in
    open L
    val pretty = pretty' Fpp.text
    val out = out' (Fpp.text o RedPrlParameterTerm.toString (fn str => str))
  end
end
