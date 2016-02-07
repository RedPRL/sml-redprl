structure Judgment : ABT_JUDGMENT =
struct
  structure Tm = Abt
  open Abt

  open Sequent

  type judgment = sequent
  type evidence = abs

  fun judgmentToString s =
    "{" ^ Sequent.toString s ^ "}"

  infix >>
  fun evidenceValence (_ >> (_, tau)) = (([],[]), tau)

  fun evidenceToString e =
    let
      infix \
      val _ \ m = outb e
    in
      DebugShowAbt.toString m
    end

  open Sequent infix >>
  fun substJudgment (x, e) (H >> (P, tau)) =
    let
      val H' =
        {metactx = #metactx H,
         symctx = #symctx H,
         hypctx = SymbolTelescope.map (#hypctx H) (fn (Q, tau) => (metasubst (e, x) Q, tau))}
    in
      H' >> (metasubst (e, x) P, tau)
    end
end
