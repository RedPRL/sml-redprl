structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

structure Lcf :
sig
  include LCF_UTIL
  val prettyState : jdg state -> Fpp.doc
end =
struct
  structure Lcf = Lcf (LcfLanguage)
  structure Def = LcfUtilPure (structure Lcf = Lcf structure J = RedPrlJudgment)
  open Def Lcf
  infix |> ||

  (* TODO: clean up all this stuff with vsep *)

  fun @@ (f, x) = f x
  infixr 0 @@

  fun prettyGoal (x, jdg) =
    Fpp.nest 2 @@ 
      Fpp.vsep 
        [Fpp.seq [Fpp.hsep [Fpp.text "Goal", Fpp.text (Metavar.toString x)], Fpp.text "."],
         RedPrlSequent.pretty TermPrinter.ppTerm jdg]

  val prettyGoals : jdg Tl.telescope -> {doc : Fpp.doc, env : J.env, idx : int} = 
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
            {doc = Fpp.seq [doc, prettyGoal (x, jdg), Fpp.newline],
             env = env',
             idx = idx + 1}
          end)
        {doc = Fpp.empty, env = Metavar.Ctx.empty, idx = 0}
    end

  fun prettyState (psi |> _) = 
    #doc (prettyGoals psi)
end
