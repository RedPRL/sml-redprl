structure RedPrlJudgment : LCF_JUDGMENT  =
struct
  structure AJ = AtomicJudgment
  structure S = Sequent
  structure Tm = RedPrlAbt
  type sort = Tm.valence
  type env = Tm.metaenv
  type ren = Tm.metavariable Tm.Metavar.Ctx.dict
  type jdg = S.jdg

  val subst = S.map o Tm.substMetaenv
  val ren = S.map o Tm.renameMetavars

  val eq = S.eq

  local
    open S
    infix >>
  in
    fun sort (H >> atjdg) =
      (Hyps.foldr (fn (_, jdg, r) => AJ.synthesis jdg :: r) [] H,
       AJ.synthesis atjdg)
  end
end
