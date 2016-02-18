structure Judgment : ABT_JUDGMENT =
struct
  structure Tm = Abt
  open Abt

  open Sequent

  type judgment = sequent
  type evidence = abs

  fun judgmentToString s =
    Sequent.toString s

  infix >>
  val rec evidenceValence =
    fn H >> concl =>
         (case concl of
             TRUE (_, tau) => (([],[]), tau)
           | TYPE _ => (([],[]), SortData.LVL))
     | GENERAL (xs, s) =>
         let
           val ((ssorts,vsorts),tau) = evidenceValence s
         in
           ((ssorts, vsorts @ List.map #2 xs), tau)
         end

  fun evidenceToString e =
    let
      infix \
      val _ \ m = outb e
    in
      ShowAbt.toString m
    end

  open Sequent infix >>
  fun substConcl (x, e) =
    fn TRUE (P, tau) => TRUE (metasubst (e,x) P, tau)
     | TYPE (P, tau) => TYPE (metasubst (e,x) P, tau)

  fun substJudgment (x, e) (H >> concl) =
    let
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = SymbolTelescope.map (fn (Q, tau) => (metasubst (e, x) Q, tau)) (#hypctx H)}
    in
      H' >> substConcl (x, e) concl
    end
    | substJudgment (x, e) (GENERAL (xs, s)) = GENERAL (xs, substJudgment (x,e) s)
end
