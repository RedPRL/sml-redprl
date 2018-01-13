structure Sequent :> SEQUENT =
struct
  structure AJ = AtomicJudgment
  structure Tm = RedPrlAbt
  structure TP = TermPrinter

  structure Tl = TelescopeUtil (Telescope (Sym))

  datatype atjdg = datatype AJ.jdg
  type abt = Tm.abt

  type hyps = {hyps: atjdg Tl.telescope, bound: Tm.variable list}

  exception todo fun ?e = raise e  

  structure Hyps = 
  struct

    fun toList {hyps, bound} =
      Tl.foldr (fn (x, jdg, r) => Tm.check (Tm.`x, AJ.synthesis jdg) :: r) [] hyps

    fun lookup {hyps, bound} z =
      Tl.lookup hyps z
      handle _ =>
        raise RedPrlError.error [Fpp.text "Found nothing in context for hypothesis", TermPrinter.ppVar z]

    fun modifyAfter x f {hyps, bound} =
      {hyps = Tl.modifyAfter x f hyps,
       bound = bound}

    fun remove x {hyps, bound} = 
      {hyps = Tl.remove x hyps, 
       bound = List.filter (fn y => not (Sym.eq (x, y))) bound}

    fun foldl f z {hyps, bound} = Tl.foldl f z hyps
    fun foldr f z {hyps, bound} = Tl.foldr f z hyps

    fun snoc {hyps, bound} x jdg =
      {hyps = Tl.snoc hyps x jdg,
       bound = x :: bound}

    val empty = {hyps = Tl.empty, bound = []}

    fun singleton x jdg = 
      {hyps = Tl.singleton x jdg,
       bound = [x]}

    fun isEmpty {hyps, bound} = Tl.isEmpty hyps

    fun map f {hyps, bound} =
      {hyps = Tl.map f hyps,
       bound = bound}

    fun modify x f {hyps, bound} =
      {hyps = Tl.modify x f hyps,
       bound = bound}

    fun truncateFrom {hyps, bound} x =
      {hyps = Tl.truncateFrom hyps x,
       bound = bound}

    (* The telescope lib should be redesigned to make the following helper functions easier.
     * At least the calling convention can be more consistent. *)

    fun substAfter (z, term) {hyps, bound} = 
      {hyps = Tl.modifyAfter z (AJ.map (Tm.substVar (term, z))) hyps,
       bound = bound}

    fun splice {hyps, bound} x (H : hyps) =
      {hyps = Tl.splice hyps x (#hyps H),
       bound = #bound H @ bound}

    fun interposeAfter (z, H' : hyps) {hyps, bound} =
      {hyps = Tl.interposeAfter hyps z (#hyps H'),
       bound = #bound H' @ bound}

    fun interposeThenSubstAfter (z, H' : hyps, term) {hyps, bound} =
      {hyps = Tl.interposeAfter (Tl.modifyAfter z (AJ.map (Tm.substVar (term, z))) hyps) z (#hyps H'),
       bound = #bound H' @ bound}

    fun pretty H : Fpp.doc =
      Fpp.vsep 
        [Fpp.vsep (foldr (fn (x, a, r) => Fpp.hsep [TP.ppVar x, Fpp.Atomic.colon, AJ.pretty a] :: r) [] H),
         Fpp.Atomic.squares
           (Fpp.hsep (List.map TermPrinter.ppVar (#bound H)))]

    local
      open Tl.ConsView
    in
      fun telescopeEq (t1, t2) =
        case (out t1, out t2) of
          (EMPTY, EMPTY) => true
        | (CONS (x, catjdg1, t1'), CONS (y, catjdg2, t2')) =>
            Sym.eq (x, y)
              andalso AJ.eq (catjdg1, catjdg2)
              andalso telescopeEq (t1', t2')
        | _ => false

      fun relabelTl H rho =
        case out H of
            EMPTY => Tl.empty
          | CONS (x, catjdg, Hx) =>
            let
              val catjdg' = AJ.map (Tm.renameVars rho) catjdg
            in
              case Var.Ctx.find rho x of
                  NONE => Tl.cons x catjdg' (relabelTl Hx rho)
                | SOME y => Tl.cons y catjdg' (relabelTl Hx rho)
            end

      fun relabel {hyps, bound} rho = 
        {hyps = relabelTl hyps rho,
         bound = List.map (fn x => Var.Ctx.lookup rho x handle _ => x) bound}
      
      fun eq (H1 : hyps, H2 : hyps) =
        telescopeEq (#hyps H1, #hyps H2)
          andalso ListPair.allEq Sym.eq (#bound H1, #bound H2) handle _ => false
    end
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


  fun relabel srho =
    fn H >> catjdg => Hyps.relabel H srho >> AJ.map (Tm.renameVars srho) catjdg
     | jdg => map (Tm.renameVars srho) jdg

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
         ruleSep (Hyps.pretty H, AJ.pretty atjdg)
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

         val H1' = Hyps.relabel H1 xrho1
         val H2' = Hyps.relabel H2 xrho2
         val catjdg1' = AJ.map (Tm.renameVars xrho1) catjdg1
         val catjdg2' = AJ.map (Tm.renameVars xrho2) catjdg2
       in
         Hyps.eq (H1', H2')
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


  fun push xs jdg =
    let
      fun clone x = Sym.named ("$" ^ Sym.toString x)
      val (xs', rho) = List.foldr (fn (x, (xs, rho)) => let val x' = clone x in (x' :: xs, Sym.Ctx.insert rho x x') end) ([], Sym.Ctx.empty) xs
      val {hyps, bound} >> ajdg = relabel rho jdg
    in
      {hyps = hyps, bound = xs' @ bound} >> ajdg
    end

  fun popAs xs' jdg =
    let
      val H as {bound, ...} >> _ = jdg
      val n = List.length xs'
      val (xs, bound') = (List.take (bound,n), List.drop (bound, n))
      val rho = ListPair.foldl (fn (x, x', rho) => Sym.Ctx.insert rho x x') Sym.Ctx.empty (xs, xs')
      val {hyps, ...} >> ajdg = relabel rho H
    in
      {bound = bound', hyps = hyps} >> ajdg
    end

  fun popSpecific xs jdg = 
    let
      val {hyps, bound} >> ajdg = jdg
    
      (* TODO: less ridiculous *)
      val bound' = List.filter (fn y => not (List.exists (fn x => Sym.eq (x, y)) xs)) bound
    in
      {hyps = hyps, bound = bound'} >> ajdg
    end

  local
    structure AJ = AtomicJudgment
    structure S = Selector
    structure O = RedPrlOpData (* TODO: we should move the selector crap out of there! *)
  in
    fun mapSelector sel f (H : hyps, catjdg) =
      case sel of
          S.IN_CONCL => (H, f catjdg)
        | S.IN_HYP x => (Hyps.modify x f H, catjdg)

    fun multiMapSelector sels f (H, catjdg) =
      List.foldl (fn (sel, state) => mapSelector sel f state) (H, catjdg) sels

    fun lookupSelector sel (H : hyps, catjdg : AJ.jdg) : AJ.jdg =
      case sel of
          S.IN_CONCL => catjdg
        | S.IN_HYP x => Hyps.lookup H x

    fun truncateFrom sel H =
      case sel of
          S.IN_CONCL => H
        | S.IN_HYP x => Hyps.truncateFrom H x
  end
end
