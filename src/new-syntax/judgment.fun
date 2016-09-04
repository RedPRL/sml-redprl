functor RedPrlJudgment (S : SEQUENT) : ABT_JUDGMENT =
struct
  structure Tm = RedPrlAbt
  type valence = Tm.valence

  structure CJ = CategoricalJudgment
  type judgment = Tm.abt CJ.jdg S.jdg
  type evidence = Tm.abs
  type metavariable = Tm.metavariable

  val judgmentToString = S.toString CJ.toString

  local
    open Tm
    infix \
  in
    fun evidenceToString e =
      case outb e of
         _ \ m => ShowAbt.toString m
  end

  val substEvidence = S.map o CJ.map o Tm.substMetavar
  val substEvidenceEnv = S.map o CJ.map o Tm.substMetaenv

  structure MetaCtx = Tm.Metavar.Ctx
  structure VarCtx = Tm.Var.Ctx
  structure SymCtx = Tm.Sym.Ctx

  local
    open S
    structure O = RedPrlOpData
    infix >> |>
  in
    val rec evidenceValence =
      fn H >> catjdg => (([],[]), CJ.synthesis catjdg)
       | (U, G) |> jdg =>
           let
             val ((sigmas, taus), tau) = evidenceValence jdg
           in
             ((List.map #2 U @ sigmas, List.map #2 G @ taus), tau)
           end
    local
      structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = RedPrlArity.Vl)
      val <+> = MetaCtxUtil.union
      infix <+>
    in
      fun hypsMetactx H : RedPrlArity.Vl.t MetaCtx.dict =
        S.Hyps.foldl
          (fn (a, psi) => psi <+> CJ.metactx a)
          MetaCtx.empty
          H

      val rec judgmentMetactx : judgment -> RedPrlArity.Vl.t MetaCtx.dict =
        fn H >> catjdg => hypsMetactx H <+> CJ.metactx catjdg
         | _ |> jdg => judgmentMetactx jdg
    end

    local
      structure MetaRenUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Tm.Metavar)
      structure SymRenUtil = ContextUtil (structure Ctx = SymCtx and Elem = Tm.Sym)
      structure VarRenUtil = ContextUtil (structure Ctx = VarCtx and Elem = Tm.Var)

      fun mergeUnification (mrho1, srho1, vrho1) (mrho2, srho2, vrho2) =
        (MetaRenUtil.union (mrho1, mrho2),
         SymRenUtil.union (srho1, srho2),
         VarRenUtil.union (vrho1, vrho2))
    in
      fun unifyHyps (tele1, tele2) : Tm.Unify.renaming =
        let
          open S.Hyps.ConsView
          fun go (mrho, srho, vrho) =
            fn (EMPTY, EMPTY) => (mrho, srho, vrho)
             | (CONS (x1, a1, tele1') , CONS (x2, a2, tele2')) =>
                 if Tm.Sym.eq (x1, x2) then
                   let
                     val (mrho', srho', vrho') = CJ.unify (a1, a2)
                     val mrho'' = MetaRenUtil.union (mrho, mrho')
                     val srho'' = SymRenUtil.union (srho, srho')
                     val vrho'' = VarRenUtil.union (vrho, vrho')
                   in
                     go (mrho'', srho'', vrho'') (out tele1', out tele2')
                   end
                 else
                   raise Tm.Unify.UnificationFailed
             | _ => raise Tm.Unify.UnificationFailed
        in
          go (MetaCtx.empty, SymCtx.empty, VarCtx.empty) (out tele1, out tele2)
        end

        val rec unifyJudgment' =
          fn (H1 >> concl1, H2 >> concl2) =>
               let
                 val rho1 = unifyHyps (H1, H2)
                 val rho2 = CJ.unify (concl1, concl2)
               in
                 mergeUnification rho1 rho2
               end
          | ((U1, G1) |> jdg1, (U2, G2) |> jdg2) =>
              let
                val _ =
                  ListPair.appEq
                    (fn ((x, sigma), (y, tau)) =>
                       if Tm.Var.eq (x, y) andalso sigma = tau then
                         ()
                       else
                         raise Tm.Unify.UnificationFailed)
                    (G1, G2)
              in
                unifyJudgment' (jdg1, jdg2)
              end
          | _ => raise Tm.Unify.UnificationFailed

        fun unifyJudgment (jdg1, jdg2) =
          SOME (unifyJudgment' (jdg1, jdg2))
            handle _ => NONE
    end
  end


end
