functor SequentJudgment
  (structure S : SEQUENT where type CJ.Tm.Sym.t = Sym.t and type CJ.Tm.Var.t = Sym.t and type CJ.Tm.O.Ar.Vl.S.t = RedPrlSort.t
   structure TermPrinter : sig type t = S.CJ.Tm.abt val ppTerm : t -> Fpp.doc end) : LCF_JUDGMENT  =
struct
  structure CJ = S.CJ
  structure Tm = CJ.Tm
  type sort = Tm.valence
  type env = Tm.metaenv
  type jdg = Tm.abt S.jdg

  val subst = S.map o Tm.substMetaenv
  val eq = S.eq
  val toString = FppRenderPlainText.toString o FinalPrinter.execPP o S.pretty Tm.eq TermPrinter.ppTerm

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
       | DIM_SUBST (r, u, m) => (([],[]), Tm.sort m)
  end
end

structure RedPrlSequent = Sequent (structure CJ = RedPrlCategoricalJudgment)
structure RedPrlJudgment = SequentJudgment (structure S = RedPrlSequent and TermPrinter = TermPrinter)
