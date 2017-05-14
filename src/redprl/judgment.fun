functor SequentJudgment
  (structure S : SEQUENT where type 'a CJ.Tm.O.Ar.Vl.Sp.t = 'a list and type CJ.Tm.Sym.t = Sym.t and type CJ.Tm.Var.t = Sym.t
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

  fun relabelHypsWithVarenv vrho = 
    let
      open S.Hyps.ConsView
      fun go EMPTY H = H
        | go (CONS (x, jdg, H')) H = 
          (case Tm.Var.Ctx.find vrho x of
              SOME tm => 
                (case Tm.out tm of
                   Tm.` y => go (out H') (S.Hyps.snoc H y jdg)
                 | _ => go (out H') (S.Hyps.snoc H x jdg))
            | _ => go (out H') (S.Hyps.snoc H x jdg))
    in
      fn H => go (out H) S.Hyps.empty
    end

  fun relabelWithVarenv vrho jdg =
    case jdg of 
       S.>> (H, catjdg) => S.>> (relabelHypsWithVarenv vrho H, catjdg)
     | _ => jdg

  val substSymenv = 
    S.map o Tm.substSymenv

  fun substVarenv vrho =
    relabelWithVarenv vrho o S.map (Tm.substVarenv vrho)

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
