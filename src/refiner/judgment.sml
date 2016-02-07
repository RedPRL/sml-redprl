structure Judgment : ABT_JUDGMENT =
struct
  structure Tm = Abt
  open Abt

  type judgment = Sequent.sequent
  type evidence = abs

  fun judgmentToString s =
    "{" ^ Sequent.toString s ^ "}"

  fun evidenceValence _ = (([],[]), SortData.EXP)

  fun evidenceToString e =
    let
      infix \
      val _ \ m = outb e
    in
      DebugShowAbt.toString m
    end

  open Sequent infix >>
  fun substJudgment (x, e) (H >> P) =
    SymbolTelescope.map H (fn (Q, tau) => (metasubst (e,x) Q, tau))
      >> metasubst (e, x) P
end
