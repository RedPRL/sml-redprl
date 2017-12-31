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
       | MATCH (th, k, _, _) =>
           let
             val (vls, _) = Tm.O.arity th
             val (_, tau) = List.nth (vls, k)
           in
             ([], tau)
           end
       | MATCH_RECORD _ => ([], RedPrlSort.EXP)
  end
end
