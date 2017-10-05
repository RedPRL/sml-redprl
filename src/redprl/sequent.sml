structure RedPrlSequent : SEQUENT =
struct
  structure AJ = RedPrlAtomicJudgment
  structure Tm = RedPrlAbt
  structure O = RedPrlOperator
  structure TP = TermPrinter
  structure PS = RedPrlParamSort
  structure P = RedPrlParameterTerm

  open RedPrlSequentData
  infix >>

  fun map f =
    fn H >> catjdg => Hyps.map (AJ.map f) H >> AJ.map f catjdg
     | MATCH (th, k, a, ps, ms) => MATCH (th, k, f a, ps, List.map f ms)
     | MATCH_RECORD (lbl, tm, tuple) => MATCH_RECORD (lbl, f tm, f tuple)

  local
    open Hyps.ConsView
  in
    fun telescopeEq (t1, t2) =
      case (out t1, out t2) of
         (EMPTY, EMPTY) => true
       | (CONS (x, catjdg1, t1'), CONS (y, catjdg2, t2')) =>
           Sym.eq (x, y)
             andalso AJ.eq (catjdg1, catjdg2)
             andalso telescopeEq (t1', t2')
       | _ => false

    fun relabelHyps H rho =
      case out H of
          EMPTY => Hyps.empty
        | CONS (x, catjdg, Hx) =>
          let
            val catjdg' = AJ.map (Tm.renameVars rho) catjdg
          in
            case Var.Ctx.find rho x of
                NONE => Hyps.cons x catjdg' (relabelHyps Hx rho)
              | SOME y => Hyps.cons y catjdg' (relabelHyps Hx rho)
          end

  end

  fun relabel srho =
    fn H >> catjdg => relabelHyps H srho >> AJ.map (Tm.renameVars srho) catjdg
     | jdg => map (Tm.renameVars srho) jdg

  fun prettyHyps f : 'a ctx -> Fpp.doc =
    Fpp.vsep o Hyps.foldr (fn (x, a, r) => Fpp.hsep [TP.ppSym x, Fpp.Atomic.colon, f a] :: r) []

  val pretty : jdg -> Fpp.doc =
    fn H >> catjdg =>
       Fpp.seq
         [if Hyps.isEmpty H then Fpp.empty else Fpp.seq [prettyHyps AJ.pretty H, Fpp.newline],
          Fpp.hsep [Fpp.text ">>", AJ.pretty catjdg]]
     | MATCH (th, k, a, _, _) => Fpp.hsep [TP.ppTerm a, Fpp.text "match", TP.ppOperator th, Fpp.text "@", Fpp.text (Int.toString k)]
     | MATCH_RECORD (lbl, a, m) => Fpp.hsep [TP.ppTerm a, Fpp.text "match_record", Fpp.text lbl, Fpp.text "with tuple", TP.ppTerm m]

  val rec eq =
    fn (H1 >> catjdg1, H2 >> catjdg2) =>
       (let
         val xs1 = Hyps.foldr (fn (x, _, xs) => x :: xs) [] H1
         val xs2 = Hyps.foldr (fn (x, _, xs) => x :: xs) [] H2
         val xs = ListPair.mapEq (fn _ => Sym.new ()) (xs1, xs2)
         val xrho1 = ListPair.foldr (fn (x1, x, rho) => Sym.Ctx.insert rho x1 x) Sym.Ctx.empty (xs1, xs)
         val xrho2 = ListPair.foldr (fn (x2, x, rho) => Sym.Ctx.insert rho x2 x) Sym.Ctx.empty (xs2, xs)

         val H1' = relabelHyps H1 xrho1
         val H2' = relabelHyps H2 xrho2
         val catjdg1' = AJ.map (Tm.renameVars xrho1) catjdg1
         val catjdg2' = AJ.map (Tm.renameVars xrho2) catjdg2
       in
         telescopeEq (H1', H2')
           andalso AJ.eq (catjdg1', catjdg2')
       end
       handle _ => false)
     | (MATCH (th1, k1, a1, ps1, ms1), MATCH (th2, k2, a2, ps2, ms2)) =>
          O.eq Sym.eq (th1, th2)
            andalso k1 = k2
            andalso Tm.eq (a1, a2)
            andalso ListPair.allEq (O.P.eq Sym.eq) (ps1, ps2)
            andalso ListPair.allEq Tm.eq (ms1, ms2)
     | (MATCH_RECORD (lbl1, a1, m1), MATCH_RECORD (lbl2, a2, m2)) =>
          lbl1 = lbl2 andalso Tm.eq (a1, a2) andalso Tm.eq (m1, m2)
     | _ => false
end

structure Selector =
struct
  local
    structure AJ = RedPrlAtomicJudgment
    structure O = RedPrlOpData (* TODO: we should move the selector crap out of there! *)
    structure Hyps = RedPrlSequentData.Hyps
  in
    fun map sel f (H : AJ.jdg Hyps.telescope, catjdg) =
      case sel of
         O.IN_CONCL => (H, AJ.map f catjdg)
       | O.IN_HYP x => (Hyps.modify x (AJ.map f) H, catjdg)

    fun multiMap sels f (H, catjdg) =
      List.foldl (fn (sel, state) => map sel f state) (H, catjdg) sels

    fun lookup sel (H : AJ.jdg Hyps.telescope, catjdg : AJ.jdg) : AJ.jdg =
      case sel of
         O.IN_CONCL => catjdg
       | O.IN_HYP x => Hyps.lookup H x

    fun truncateFrom sel H =
      case sel of
         O.IN_CONCL => H
       | O.IN_HYP x => Hyps.truncateFrom H x
  end
end