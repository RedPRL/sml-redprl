functor SequentJudgment
  (structure S : SEQUENT where type 'a CJ.Tm.O.Ar.Vl.Sp.t = 'a list
   structure TermPrinter : SHOW where type t = S.CJ.Tm.abt) : LCF_JUDGMENT =
struct
  structure CJ = S.CJ
  structure Tm = CJ.Tm
  type sort = Tm.valence
  type env = Tm.metaenv
  type jdg = Tm.abt S.jdg

  val subst = S.map o Tm.substMetaenv
  val eq = S.eq
  val toString = S.toString TermPrinter.toString


  local
    open S
    infix >> |>
  in
    val rec sort =
      fn H >> catjdg => (([],[]), CJ.synthesis catjdg)
       | MATCH (th, k, _) =>
           let
             val (vls, _) = Tm.O.arity th
           in
             List.nth (vls, k)
           end
       | (U, G) |> jdg =>
           let
             val ((sigmas, taus), tau) = sort jdg
           in
             ((List.map #2 U @ sigmas, List.map #2 G @ taus), tau)
           end
  end
end

structure RedPrlSequent = Sequent (structure CJ = RedPrlCategoricalJudgment)
structure RedPrlJudgment = SequentJudgment (structure S = RedPrlSequent and TermPrinter = TermPrinter)
