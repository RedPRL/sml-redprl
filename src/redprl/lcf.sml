structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

structure Lcf :
sig
  include LCF_TACTIC
  val prettyState : jdg state -> Fpp.doc
end =
struct
  structure Lcf = Lcf (LcfLanguage)
  structure Def = LcfTactic (structure J = RedPrlJudgment and Lcf = Lcf and M = LcfTacticMonad)
  open Def Lcf
  infix |> ||

  (* TODO: clean up all this stuff with vsep *)
  (* TODO: also try to extend the printer with "concrete name" environments so that we can print without doing
     all these renamings. *)

  fun @@ (f, x) = f x
  infixr 0 @@

  fun prettyGoal (x, jdg) =
    Fpp.nest 2 @@
      Fpp.vsep
        [Fpp.seq [Fpp.hsep [Fpp.text "Goal", TermPrinter.ppMeta x], Fpp.text "."],
         Sequent.pretty jdg]

  val prettyGoals : jdg Tl.telescope -> {doc : Fpp.doc, ren : J.ren, idx : int} =
    let
      open RedPrlAbt
    in
      Tl.foldl
        (fn (x, jdg, {doc, ren, idx}) =>
          let
            val x' = Metavar.named (Int.toString idx)
            val jdg' = J.ren ren jdg
            val ren' = Metavar.Ctx.insert ren x x'
          in
            {doc = Fpp.seq [doc, prettyGoal (x', jdg'), Fpp.newline],
             ren = ren',
             idx = idx + 1}
          end)
        {doc = Fpp.empty, ren = Metavar.Ctx.empty, idx = 0}
    end

  fun prettyState (psi |> _) =
    #doc (prettyGoals psi)
end
