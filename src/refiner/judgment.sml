structure Judgment : ABT_JUDGMENT =
struct
  structure Tm = Abt
  open Abt

  open Sequent

  type judgment = generic
  type evidence = abs

  fun judgmentToString s =
    Sequent.toString s

  infix 4 >>
  infix 3 |>

  val rec evidenceValence =
    fn G |> H >> concl =>
         (case concl of
             TRUE (_, tau) => (([], List.map #2 G), tau)
           | TYPE _ => (([], List.map #2 G), SortData.LVL))

  fun evidenceToString e =
    let
      infix \
      val _ \ m = outb e
    in
      ShowAbt.toString m
    end

  fun substConcl rho =
    fn TRUE (P, tau) => TRUE (metasubstEnv rho P, tau)
     | TYPE (P, tau) => TYPE (metasubstEnv rho P, tau)

  structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)

  fun substEvidenceEnv rho (G |> H >> concl) =
    let
      infix \
      val hypctx' = SymbolTelescope.map (fn (Q, tau) => (metasubstEnv rho Q, tau)) (#hypctx H)
      val concl' = substConcl rho concl
      val metactx' =
        MetaCtx.foldl
          (fn (k, vl, acc) =>
             case Option.map outb (MetaCtx.find rho k) of
                 NONE => MetaCtx.insert acc k vl
               | SOME (_ \ m) => MetaCtxUtil.union (acc, metactx m))
          MetaCtx.empty
          (#metactx H)

      val H' =
        {metactx = metactx',
         symctx = #symctx H,
         hypctx = hypctx'}
    in
      G |> H' >> substConcl rho concl
    end

  fun singletonEnv (e, x) =
    MetaCtx.insert MetaCtx.empty x e

  val substEvidence =
    substEvidenceEnv
      o singletonEnv

  fun judgmentMetactx (G |> H >> concl) =
    #metactx H

  fun unifyJudgment (G1 |> H1 >> concl1, G2 |> H2 >> concl2) =
    raise Match
end
