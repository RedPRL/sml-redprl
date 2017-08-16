structure RedPrlJudgment : LCF_JUDGMENT  =
struct
  structure CJ = RedPrlCategoricalJudgment
  structure S = struct open RedPrlSequentData RedPrlSequent end
  structure Tm = RedPrlAbt
  type sort = Tm.valence
  type env = Tm.metaenv
  type ren = Tm.metavariable Tm.Metavar.Ctx.dict
  type jdg = S.jdg

  val subst = S.map o Tm.substMetaenv
  val ren = S.map o Tm.renameMetavars

  val eq = S.eq
  val toString = FppRenderPlainText.toString o FinalPrinter.execPP o S.pretty

  local
    open S
    infix >>
  in
    val rec sort =
      fn (I, H) >> catjdg =>
           ((List.map #2 I, Hyps.foldr (fn (_, jdg, r) => CJ.synthesis jdg :: r) [] H),
            CJ.synthesis catjdg)
       | MATCH (th, k, _, _, _) =>
           let
             val (vls, _) = Tm.O.arity th
             val (_, tau) = List.nth (vls, k)
           in
             (([],[]), tau)
           end
       | MATCH_RECORD (lbl, _) => (([],[]), RedPrlSortData.EXP)
  end
end
