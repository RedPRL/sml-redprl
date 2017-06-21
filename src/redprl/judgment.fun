functor SequentJudgment
  (structure S : SEQUENT where type 'a CJ.Tm.O.Ar.Vl.Sp.t = 'a list and type CJ.Tm.Sym.t = Sym.t and type CJ.Tm.Var.t = Sym.t
   structure TermPrinter : SHOW where type t = S.CJ.Tm.abt) : LCF_JUDGMENT  =
struct
  structure CJ = S.CJ
  structure Tm = CJ.Tm
  type sort = Tm.valence
  type env = Tm.metaenv
  type jdg = Tm.abt S.jdg
  type symenv = Tm.symenv
  type varenv = Tm.varenv

  val subst = S.map o Tm.substMetaenv
  val eq = S.eq
  fun toString _ = "TODO"
  (* S.toString TermPrinter.toString*)

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
  end
end
 
structure RedPrlSequent = Sequent (structure CJ = RedPrlCategoricalJudgment)
structure RedPrlJudgment = SequentJudgment (structure S = RedPrlSequent and TermPrinter = TermPrinter)
