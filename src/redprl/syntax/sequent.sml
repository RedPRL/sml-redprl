structure Sequent :> SEQUENT =
struct
  structure AJ = AtomicJudgment
  structure Tm = RedPrlAbt
  structure TP = TermPrinter

  datatype atjdg = datatype AJ.jdg
  type abt = Tm.abt

  structure Tl = 
  struct
    structure Tl = TelescopeUtil (Telescope (Sym))
    open Tl

    fun toList H =
      Tl.foldr (fn (x, jdg, r) => Tm.check (Tm.`x, AJ.synthesis jdg) :: r) [] H

    fun lookup H z =
      Tl.lookup H z
      handle _ =>
        raise RedPrlError.error [Fpp.text "Found nothing in context for hypothesis", TermPrinter.ppVar z]

    (* The telescope lib should be redesigned to make the following helper functions easier.
     * At least the calling convention can be more consistent. *)

    fun substAfter (z, term) H = (* favonia: or maybe (term, z)? I do not know. *)
      Tl.modifyAfter z (AJ.map (Tm.substVar (term, z))) H

    fun interposeAfter (z, H') H =
      Tl.interposeAfter H z H'

    fun interposeThenSubstAfter (z, H', term) H =
      Tl.interposeAfter (Tl.modifyAfter z (AJ.map (Tm.substVar (term, z))) H) z H'
  end

  type hyps = atjdg Tl.telescope

  structure Hyps = 
  struct
    open Tl
  end  

  datatype jdg =
     (* sequents / formal hypothetical judgment *)
     >> of hyps * atjdg
     (* unify a term w/ a head operator and extract the kth subterm *)
   | MATCH of RedPrlAbt.operator * int * Tm.abt * Tm.abt list
     (* unify a term w/ RECORD and extract the type of the label;
      * the third argument is the tuple. *)
   | MATCH_RECORD of string * Tm.abt * Tm.abt

  infix >>

  fun map f =
    fn H >> catjdg => Hyps.map (AJ.map f) H >> AJ.map f catjdg
     | MATCH (th, k, a, ms) => MATCH (th, k, f a, List.map f ms)
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

  val prettyHyps : hyps -> Fpp.doc =
    Fpp.vsep o Hyps.foldr (fn (x, a, r) => Fpp.hsep [TP.ppVar x, Fpp.Atomic.colon, AJ.pretty a] :: r) []

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
         ruleSep (prettyHyps H, AJ.pretty atjdg)
     | MATCH (th, k, a, _) => Fpp.hsep [TP.ppTerm a, Fpp.text "match", TP.ppOperator th, Fpp.text "@", Fpp.text (Int.toString k)]
     | MATCH_RECORD (lbl, a, m) => Fpp.hsep [TP.ppTerm a, Fpp.text "match-record", Fpp.text lbl, Fpp.text "with tuple", TP.ppTerm m]

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
     | (MATCH (th1, k1, a1, ms1), MATCH (th2, k2, a2, ms2)) =>
          Tm.O.eq (th1, th2)
            andalso k1 = k2
            andalso Tm.eq (a1, a2)
            andalso ListPair.allEq Tm.eq (ms1, ms2)
     | (MATCH_RECORD (lbl1, a1, m1), MATCH_RECORD (lbl2, a2, m2)) =>
          lbl1 = lbl2 andalso Tm.eq (a1, a2) andalso Tm.eq (m1, m2)
     | _ => false



  local
    structure AJ = AtomicJudgment
    structure S = Selector
    structure O = RedPrlOpData (* TODO: we should move the selector crap out of there! *)
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
