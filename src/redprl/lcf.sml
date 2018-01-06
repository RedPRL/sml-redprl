structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

structure Lcf :
sig
  type trace = string list
  datatype 'a traced = ::@ of trace * 'a

  include LCF_TACTIC where type 'a I.t = 'a traced
  val prettyState : jdg state -> Fpp.doc
end =
struct
  structure Tr = LcfListTrace (type e = string)
  structure Lcf = TracedLcf (structure L = LcfLanguage and Tr = Tr)
  structure Def = LcfTactic (structure J = RedPrlJudgment and Lcf = Lcf and M = LcfMonadBT)
  open Def Lcf
  infix |> ::@ ||

  (* TODO: clean up all this stuff with vsep *)
  (* TODO: also try to extend the printer with "concrete name" environments so that we can print without doing
     all these renamings. *)

  fun @@ (f, x) = f x
  infixr 0 @@

  fun prettyTrace tr = 
    Fpp.collection (Fpp.char #"[") (Fpp.char #"]") (Fpp.Atomic.comma) 
      (List.map Fpp.text tr)

  fun prettyGoal (x, tr ::@ jdg) =
    Fpp.nest 2 @@
      Fpp.vsep @@
        (Fpp.seq [Fpp.hsep [Fpp.text "Goal", TermPrinter.ppMeta x], Fpp.text "."]) ::
        (if !Config.printTrace
         then [Fpp.hsep [Fpp.text "Trace:", Fpp.align @@ prettyTrace tr], Sequent.pretty jdg]
         else [Sequent.pretty jdg])

  val prettyGoals : jdg I.t Tl.telescope -> {doc : Fpp.doc, ren : J.ren, idx : int} =
    let
      open RedPrlAbt
    in
      Tl.foldl
        (fn (x, tr ::@ jdg, {doc, ren, idx}) =>
          let
            val x' = Metavar.named (Int.toString idx)
            val jdg' = J.ren ren jdg
            val ren' = Metavar.Ctx.insert ren x x'
          in
            {doc = Fpp.seq [doc, if idx = 0 then Fpp.empty else Fpp.newline, prettyGoal (x', tr ::@ jdg')],
             ren = ren',
             idx = idx + 1}
          end)
        {doc = Fpp.empty, ren = Metavar.Ctx.empty, idx = 0}
    end

  fun prettyState (psi |> _) =
    #doc (prettyGoals psi)
end
