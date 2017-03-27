functor SequentJudgment
  (structure S : SEQUENT where type 'a CJ.Tm.O.Ar.Vl.Sp.t = 'a list
   structure TermPrinter : SHOW where type t = S.CJ.Tm.abt) : LCF_BINDING_JUDGMENT =
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
  val toString = S.toString TermPrinter.toString

  val substSymenv = S.map o Tm.substSymenv
  val substVarenv = S.map o Tm.substVarenv

  local
    open S
    infix >>
  in
    val rec sort =
      fn H >> catjdg => (([],[]), CJ.synthesis catjdg)
       | MATCH (th, k, _) =>
           let
             val (vls, _) = Tm.O.arity th
           in
             List.nth (vls, k)
           end
  end
end

structure RedPrlSequent = Sequent (structure CJ = RedPrlCategoricalJudgment)
structure RedPrlJudgment = SequentJudgment (structure S = RedPrlSequent and TermPrinter = TermPrinter)
