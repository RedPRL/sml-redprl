structure RedPrlJudgment : LCF_JUDGMENT  =
struct
  structure AJ = AtomicJudgment
  structure S = struct open SequentData Sequent end
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
    val rec sort =
      fn H >> catjdg =>
           (Hyps.foldr (fn (_, jdg, r) => AJ.synthesis jdg :: r) [] H,
            AJ.synthesis catjdg)
  end
end
