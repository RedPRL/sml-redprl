structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

structure Lcf :
sig
  include LCF_UTIL
  val prettyState : jdg state -> PP.doc
end =
struct
  structure Lcf = Lcf (LcfLanguage)
  structure Def = LcfUtilPure (structure Lcf = Lcf structure J = RedPrlJudgment)
  open Def Lcf
  infix |> ||


  val prettySyms =
    PP.text o ListSpine.pretty (fn (u, sigma) => Sym.toString u ^ " : " ^ RedPrlAbt.O.Ar.Vl.PS.toString sigma) ", "

  val prettyVars = 
    PP.text o ListSpine.pretty (fn (x, tau) => Var.toString x ^ " : " ^ RedPrlAbt.O.Ar.Vl.S.toString tau) ", "

  fun prettyGoal (x, jdg) =
    PP.concat
      [PP.text "Goal ",
        PP.text (RedPrlAbt.Metavar.toString x),
        PP.text ".",
        PP.nest 2 (PP.concat [PP.line, RedPrlSequent.pretty TermPrinter.toString jdg]),
        PP.line]


  val prettyGoals : jdg eff Tl.telescope -> {doc : PP.doc, env : J.env, idx : int} =
    let
      open RedPrlAbt
    in
      Tl.foldl
        (fn (x, jdg, {doc, env, idx}) =>
          let
            val x' = Metavar.named (Int.toString idx)
            val jdg' = J.subst env jdg
            val env' = Metavar.Ctx.insert env x (LcfLanguage.var x' (J.sort jdg'))
          in
            {doc = PP.concat [doc, prettyGoal (x, jdg), PP.line],
             env = env',
             idx = idx + 1}
          end)
        {doc = PP.empty, env = Metavar.Ctx.empty, idx = 0}
    end

  fun prettyValidation _(*env*) vld =
    let
      open RedPrlAbt infix \
      val _ \ m = outb vld
    in
      PP.concat
        [PP.text (TermPrinter.toString m),
         PP.line,
         PP.text (primToStringAbs vld)]
    end

  fun prettyState (psi |> vld) =
    let
      val {doc = goals, env, idx = _} = prettyGoals psi
    in
      PP.concat
        [goals,
         PP.newline,
         PP.rule #"-",
         PP.newline,
         PP.text "Current Proof Extract:",
         PP.newline,
         PP.rule #"-",
         PP.newline, PP.newline,
         prettyValidation env vld]
    end
end
