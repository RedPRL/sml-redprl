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

  fun substConcl (x, e) =
    fn TRUE (P, tau) => TRUE (metasubst (e,x) P, tau)
     | TYPE (P, tau) => TYPE (metasubst (e,x) P, tau)

  fun substJudgment (x, e) (G |> H >> concl) =
    let
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = SymbolTelescope.map (fn (Q, tau) => (metasubst (e, x) Q, tau)) (#hypctx H)}
    in
      G |> H' >> substConcl (x, e) concl
    end
end
