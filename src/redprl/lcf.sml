structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

signature LCF_GENERIC_UTIL = 
sig
  structure Abt : ABT
  datatype 'a generic = || of ((Abt.symbol * Abt.psort) list * (Abt.variable * Abt.sort) list) * 'a
  include LCF_UTIL where type 'a Eff.t = 'a generic
end

structure Lcf :
sig
  include LCF_GENERIC_UTIL
  val prettyState : jdg state -> PP.doc
  val stateToString : jdg state -> string
end =
struct
  structure LcfGeneric = LcfGeneric (LcfLanguage)
  structure Def = LcfGenericUtil (structure Lcf = LcfGeneric and J = RedPrlJudgment)
  open Def LcfGeneric
  infix |> ||


  val prettySyms =
    PP.text o ListSpine.pretty (fn (u, sigma) => Sym.toString u ^ " : " ^ Abt.O.Ar.Vl.PS.toString sigma) ", "

  val prettyVars = 
    PP.text o ListSpine.pretty (fn (x, tau) => Var.toString x ^ " : " ^ Abt.O.Ar.Vl.S.toString tau) ", "

  fun prettyGoal (syms, vars) (x, jdg) =
    let
      val parametric = 
        if List.length syms > 0 then
          PP.concat [PP.line, PP.text "{", prettySyms syms, PP.text "}. "]
        else
          PP.empty
      val generic = 
        if List.length vars > 0 then
          PP.concat [PP.line, PP.text "[", prettyVars vars, PP.text "]. "]
        else
          PP.empty
    in
      PP.concat
        [PP.text "Goal ",
         PP.text (RedPrlAbt.Metavar.toString x),
         PP.text ".",
         parametric,
         generic,
         PP.nest 2 (PP.concat [PP.line, RedPrlSequent.pretty TermPrinter.toString jdg]),
         PP.line]
    end


  val prettyGoals : jdg eff Tl.telescope -> {doc : PP.doc, env : J.env, idx : int} =
    let
      open RedPrlAbt
    in
      Tl.foldl
        (fn (x, (syms, vars) || jdg, {doc, env, idx}) =>
          let
            val x' = Metavar.named (Int.toString idx)
            val jdg' = J.subst env jdg
            val ((ssorts, vsorts), tau) = J.sort jdg'
            val vl' = ((ssorts @ List.map #2 syms, vsorts @ List.map #2 vars), tau)
            val env' = Metavar.Ctx.insert env x (LcfLanguage.var x' vl')
          in
            {doc = PP.concat [doc, prettyGoal (syms, vars) (x, jdg), PP.line],
             env = env',
             idx = idx + 1}
          end)
        {doc = PP.empty, env = Metavar.Ctx.empty, idx = 0}
    end

  fun prettyValidation env vld =
    let
      open RedPrlAbt infix \
      val (us,xs) \ m = outb vld
    in
      PP.concat
        [PP.text (TermPrinter.toString m),
         PP.line,
         PP.text (primToStringAbs vld)]
    end

  fun prettyState (psi |> vld) =
    let
      val {doc = goals, env, idx} = prettyGoals psi
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

  val stateToString : jdg state -> string =
    PP.toString 80 false o prettyState
end
