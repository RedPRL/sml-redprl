structure Sequent : SEQUENT =
struct
  structure AJ = AtomicJudgment
  structure Tm = RedPrlAbt
  structure TP = TermPrinter

  datatype atjdg = datatype AJ.jdg

  open SequentData
  infix >>

  fun map f =
    fn H >> catjdg => Hyps.map (AJ.map f) H >> AJ.map f catjdg

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

  fun prettyHyps f : 'a ctx -> Fpp.doc =
    Fpp.vsep o Hyps.foldr (fn (x, a, r) => Fpp.hsep [TP.ppVar x, Fpp.Atomic.colon, f a] :: r) []

  local
    fun >>= (m, k) = Fpp.bind m k
    infix >>=
    open FppBasis FppBasis.Monad FppTypes
  in
    fun measureDoc m =
      censor (fn _ => NULL)
        (getState >>= (fn oldState =>
          m >>= (fn _ =>
            askEnv >>= (fn {nesting, ...} =>
              getState >>= (fn {maxWidthSeen = w, ...} =>
                modifyState (fn _ => oldState) >>= (fn _ => 
                  ret (Space.sum (w, Space.neg nesting))))))))

    fun ruleSep (m1 : Fpp.doc, m2 : Fpp.doc) : Fpp.doc =
      measureDoc (Fpp.vsep [m1, m2]) >>= (fn w =>
        Fpp.vsep
          [m1,
           Fpp.text (CharVector.tabulate (w, fn _ => #"-")),
           m2])
  end

  val pretty : jdg -> Fpp.doc =
    fn H >> atjdg =>
       if Hyps.isEmpty H then
         AJ.pretty atjdg 
       else
         ruleSep (prettyHyps AJ.pretty H, AJ.pretty atjdg)

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

  local
    structure AJ = AtomicJudgment
    structure S = Selector
    structure O = RedPrlOpData (* TODO: we should move the selector crap out of there! *)
    structure Hyps = SequentData.Hyps
  in
    fun mapSelector sel f (H : AJ.jdg Hyps.telescope, catjdg) =
      case sel of
          S.IN_CONCL => (H, f catjdg)
        | S.IN_HYP x => (Hyps.modify x f H, catjdg)

    fun multiMapSelector sels f (H, catjdg) =
      List.foldl (fn (sel, state) => mapSelector sel f state) (H, catjdg) sels

    fun lookupSelector sel (H : AJ.jdg Hyps.telescope, catjdg : AJ.jdg) : AJ.jdg =
      case sel of
          S.IN_CONCL => catjdg
        | S.IN_HYP x => Hyps.lookup H x

    fun truncateFrom sel H =
      case sel of
          S.IN_CONCL => H
        | S.IN_HYP x => Hyps.truncateFrom H x
  end
end
