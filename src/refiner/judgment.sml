structure Judgment : ABT_JUDGMENT =
struct
  structure Tm = Abt
  open Abt

  open Sequent

  type judgment = generic
  type evidence = abs

  fun judgmentToString s =
    Sequent.toString s

  infix 4 >>
  infix 3 |>

  val conclEvidenceSort =
    fn TRUE (_, tau) => tau
     | TYPE _ => SortData.LVL
     | EQ_MEM _ => SortData.EXP
     | MEM _ => SortData.EXP
     | EQ_SYN _ => SortData.EXP
     | SYN _ => SortData.EXP

  fun evidenceValence (G |> H >> concl) =
    (([], List.map #2 G), conclEvidenceSort concl)

  fun evidenceToString e =
    let
      infix \
      val _ \ m = outb e
    in
      ShowAbt.toString m
    end

  fun substConcl rho =
    fn TRUE (a, tau) => TRUE (metasubstEnv rho a, tau)
     | TYPE (a, tau) => TYPE (metasubstEnv rho a, tau)
     | EQ_MEM (m, n, a) => EQ_MEM (metasubstEnv rho m, metasubstEnv rho n, metasubstEnv rho a)
     | MEM (m, a) => MEM (metasubstEnv rho m, metasubstEnv rho a)
     | EQ_SYN (r, s) => EQ_SYN (metasubstEnv rho r, metasubstEnv rho s)
     | SYN r => SYN (metasubstEnv rho r)

  structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)
  structure MetaRenUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Metavariable)
  structure SymRenUtil = ContextUtil (structure Ctx = SymCtx and Elem = Symbol)
  structure VarRenUtil = ContextUtil (structure Ctx = VarCtx and Elem = Variable)

  fun substEvidenceEnv rho (G |> H >> concl) =
    let
      infix \
      val concl' = substConcl rho concl

      val goHyps = SymbolTelescope.map (fn (Q, tau) => (metasubstEnv rho Q, tau))
      val goMetas =
        MetaCtx.foldl
          (fn (k, vl, acc) =>
             case Option.map outb (MetaCtx.find rho k) of
                 NONE => MetaCtx.insert acc k vl
               | SOME (_ \ m) => MetaCtxUtil.union (acc, metactx m))
          MetaCtx.empty

      val goCtx = updateHyps goHyps o updateMetas goMetas
    in
      G |> goCtx H >> substConcl rho concl
    end

  fun singletonEnv (e, x) =
    MetaCtx.insert MetaCtx.empty x e

  val substEvidence =
    substEvidenceEnv
      o singletonEnv

  val conclMetactx =
    fn TRUE (p, _) => metactx p
     | TYPE (p, _) => metactx p
     | EQ_MEM (m, n, a) => MetaCtxUtil.union (MetaCtxUtil.union (metactx m, metactx n), metactx a)
     | MEM (m, a) => MetaCtxUtil.union (metactx m, metactx a)
     | EQ_SYN (r, s) => MetaCtxUtil.union (metactx r, metactx s)
     | SYN r => metactx r

  fun hypsMetactx hyps =
    SymbolTelescope.foldl
      (fn ((p, _), acc) => MetaCtxUtil.union (acc, metactx p))
      MetaCtx.empty
      hyps

  fun judgmentMetactx (G |> H >> concl) =
    MetaCtxUtil.union (hypsMetactx (getHyps H), MetaCtxUtil.union (getMetas H, conclMetactx concl))

  (* Code review needed below: *)

  fun unifyHypotheses (tele1, tele2) : Abt.Unify.renaming =
    let
      open SymbolTelescope.ConsView
      fun go (mrho, srho, vrho) =
        fn (EMPTY, EMPTY) => (mrho, srho, vrho)
         | (CONS (x1, (a1, _), tele1') , CONS (x2, (a2, _), tele2')) =>
             if Variable.eq (x1, x2) then
               let
                 val (mrho', srho', vrho') = Abt.Unify.unify (a1, a2)
                 val mrho'' = MetaRenUtil.union (mrho, mrho')
                 val srho'' = SymRenUtil.union (srho, srho')
                 val vrho'' = VarRenUtil.union (vrho, vrho')
               in
                 go (mrho'', srho'', vrho'') (out tele1', out tele2')
               end
             else
               raise Abt.Unify.UnificationFailed
         | _ => raise Abt.Unify.UnificationFailed
    in
      go (MetaCtx.empty, SymCtx.empty, VarCtx.empty) (out tele1, out tele2)
    end

  fun mergeUnification (mrho1, srho1, vrho1) (mrho2, srho2, vrho2) =
    (MetaRenUtil.union (mrho1, mrho2),
     SymRenUtil.union (srho1, srho2),
     VarRenUtil.union (vrho1, vrho2))

  val unifyConcl =
    fn (TRUE (p1, _), TRUE (p2, _)) => Abt.Unify.unify (p1, p2)
     | (TYPE (p1, _), TYPE (p2, _)) => Abt.Unify.unify (p1, p2)
     | (EQ_MEM (m1, n1, a1), EQ_MEM (m2, n2, a2)) =>
         let
           val rho1 = Abt.Unify.unify (m1, m2)
           val rho2 = Abt.Unify.unify (n1, n2)
           val rho3 = Abt.Unify.unify (a1, a2)
         in
           mergeUnification (mergeUnification rho1 rho2) rho3
         end
     | (MEM (m1, a1), MEM (m2, a2)) =>
         let
           val rho1 = Abt.Unify.unify (m1, m2)
           val rho2 = Abt.Unify.unify (a1, a2)
         in
           mergeUnification rho1 rho2
         end
     | (EQ_SYN (r1, s1), EQ_SYN (r2, s2)) =>
         let
           val rho1 = Abt.Unify.unify (r1, r2)
           val rho2 = Abt.Unify.unify (s1, s2)
         in
           mergeUnification rho1 rho2
         end
     | (SYN r1, SYN r2) =>
         Abt.Unify.unify (r1, r2)
     | _ => raise Abt.Unify.UnificationFailed

  fun unifyJudgment' (G1 |> H1 >> concl1, G2 |> H2 >> concl2) : Abt.Unify.renaming =
    let
      val rho1 = unifyHypotheses (getHyps H1, getHyps H2)
      val rho2 = unifyConcl (concl1, concl2)
    in
      mergeUnification rho1 rho2
    end

  fun unifyJudgment (jdg1, jdg2) =
    SOME (unifyJudgment' (jdg1, jdg2))
    handle _ => NONE
end
