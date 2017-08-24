structure RedPrlSequent : SEQUENT =
struct
  structure CJ = RedPrlCategoricalJudgment
  structure Tm = RedPrlAbt
  structure O = RedPrlOperator
  structure TP = TermPrinter
  structure PS = RedPrlParamSort
  structure P = RedPrlParameterTerm

  open RedPrlSequentData
  infix >>
  type jdg = Tm.abt jdg'

  fun map f =
    fn (I, H) >> catjdg => (I, Hyps.map (CJ.map f) H) >> CJ.map f catjdg
     | MATCH (th, k, a, ps, ms) => MATCH (th, k, f a, ps, List.map f ms)
     | MATCH_RECORD (lbl, tm) => MATCH_RECORD (lbl, f tm)

  fun renameHypsInTerm srho =
    Tm.substSymenv (Sym.Ctx.map P.VAR srho)
      o Tm.renameVars srho

  local
    open Hyps.ConsView
  in
    fun telescopeEq (t1, t2) =
      case (out t1, out t2) of
         (EMPTY, EMPTY) => true
       | (CONS (x, catjdg1, t1'), CONS (y, catjdg2, t2')) =>
           Sym.eq (x, y)
             andalso CJ.eq (catjdg1, catjdg2)
             andalso telescopeEq (t1', t2')
       | _ => false

    fun relabelHyps H srho =
      let
        val srho' = Sym.Ctx.map P.VAR srho
      in
        case out H of
           EMPTY => Hyps.empty
         | CONS (x, catjdg, Hx) =>
           let
             val catjdg' = CJ.map (Tm.substSymenv srho') catjdg
           in
             case Sym.Ctx.find srho x of
                 NONE => Hyps.cons x catjdg' (relabelHyps Hx srho)
               | SOME y => Hyps.cons y catjdg' (relabelHyps Hx srho)
           end
      end

  end

  fun relabel srho =
    fn (I, H) >> catjdg =>
       (List.map (fn (u, sigma) => (Sym.Ctx.lookup srho u handle _ => u, sigma)) I, relabelHyps H srho)
         >> CJ.map (renameHypsInTerm srho) catjdg
     | jdg => map (renameHypsInTerm srho) jdg

  fun prettySyms syms =
    Fpp.collection
      (Fpp.char #"{")
      (Fpp.char #"}")
      (Fpp.Atomic.comma)
      (List.map (fn (u, sigma) => Fpp.hsep [TP.ppSym u, Fpp.Atomic.colon, Fpp.text (PS.toString sigma)]) syms)

  fun prettyHyps f : 'a ctx -> Fpp.doc =
    Fpp.vsep o Hyps.foldr (fn (x, a, r) => Fpp.hsep [TP.ppSym x, Fpp.Atomic.colon, f a] :: r) []

  val pretty : jdg -> Fpp.doc =
    fn (I, H) >> catjdg =>
       Fpp.seq
         [case I of [] => Fpp.empty | _ => Fpp.seq [prettySyms I, Fpp.newline],
          if Hyps.isEmpty H then Fpp.empty else Fpp.seq [prettyHyps CJ.pretty H, Fpp.newline],
          Fpp.hsep [Fpp.text ">>", CJ.pretty catjdg]]
     | MATCH (th, k, a, _, _) => Fpp.hsep [TP.ppTerm a, Fpp.text "match", TP.ppOperator th, Fpp.text "@", Fpp.text (Int.toString k)]
     | MATCH_RECORD (lbl, a) => Fpp.hsep [TP.ppTerm a, Fpp.text "match_record", Fpp.text lbl]

  val rec eq =
    fn ((I1, H1) >> catjdg1, (I2, H2) >> catjdg2) =>
       (let
         fun unifyPsorts (sigma1, sigma2) =
           if PS.eq (sigma1, sigma2) then sigma1 else
             raise Fail "psort mismatch in Sequent.eq"

         val I = ListPair.mapEq (fn ((_, sigma1), (_, sigma2)) => (Sym.new (), unifyPsorts (sigma1, sigma2))) (I1, I2)
         val srho1 = ListPair.foldr (fn ((u1, _), (u, _), rho) => Sym.Ctx.insert rho u1 (P.ret u)) Sym.Ctx.empty (I1, I)
         val srho2 = ListPair.foldr (fn ((u2, _), (u, _), rho) => Sym.Ctx.insert rho u2 (P.ret u)) Sym.Ctx.empty (I2, I)

         val xs1 = Hyps.foldr (fn (x, _, xs) => x :: xs) [] H1
         val xs2 = Hyps.foldr (fn (x, _, xs) => x :: xs) [] H2
         val xs = ListPair.mapEq (fn _ => Sym.new ()) (xs1, xs2)
         val xrho1 = ListPair.foldr (fn (x1, x, rho) => Sym.Ctx.insert rho x1 x) Sym.Ctx.empty (xs1, xs)
         val xrho2 = ListPair.foldr (fn (x2, x, rho) => Sym.Ctx.insert rho x2 x) Sym.Ctx.empty (xs2, xs)

         val H1' = Hyps.map (CJ.map (Tm.substSymenv srho1)) (relabelHyps H1 xrho1)
         val H2' = Hyps.map (CJ.map (Tm.substSymenv srho2)) (relabelHyps H2 xrho2)
         val catjdg1' = CJ.map (Tm.substSymenv srho1 o renameHypsInTerm xrho1) catjdg1
         val catjdg2' = CJ.map (Tm.substSymenv srho2 o renameHypsInTerm xrho2) catjdg2
       in
         telescopeEq (H1', H2')
           andalso CJ.eq (catjdg1', catjdg2')
       end
       handle _ => false)
     | (MATCH (th1, k1, a1, ps1, ms1), MATCH (th2, k2, a2, ps2, ms2)) =>
          O.eq Sym.eq (th1, th2)
            andalso k1 = k2
            andalso Tm.eq (a1, a2)
            andalso ListPair.allEq (O.P.eq Sym.eq) (ps1, ps2)
            andalso ListPair.allEq Tm.eq (ms1, ms2)
     | (MATCH_RECORD (lbl1, a1), MATCH_RECORD (lbl2, a2)) =>
          lbl1 = lbl2 andalso Tm.eq (a1, a2)
     | _ => false
end
