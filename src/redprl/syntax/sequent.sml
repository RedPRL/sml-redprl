structure Sequent :> SEQUENT =
struct
  structure AJ = AtomicJudgment
  structure Tm = RedPrlAbt
  structure TP = TermPrinter

  structure Tl = TelescopeUtil (Telescope (Sym))

  datatype atjdg = datatype AJ.jdg
  type abt = Tm.abt
  type variable = Tm.variable

  type hidden = Tm.variable * string option
  type hyps = {hyps: atjdg Tl.telescope, hidden: hidden list}

  exception todo fun ?e = raise e  

  structure Hyps = 
  struct

    fun toList {hyps, hidden} =
      Tl.foldr (fn (x, jdg, r) => Tm.check (Tm.`x, AJ.synthesis jdg) :: r) [] hyps

    fun lookup {hyps, hidden} z =
      Tl.lookup hyps z
      handle _ =>
        raise RedPrlError.error [Fpp.text "Found nothing in context for hypothesis", TermPrinter.ppVar z]

    fun modifyAfter x f {hyps, hidden} =
      {hyps = Tl.modifyAfter x f hyps,
       hidden = hidden}

    fun remove x {hyps, hidden} = 
      {hyps = Tl.remove x hyps, 
       hidden = List.filter (fn (y, _) => not (Sym.eq (x, y))) hidden}

    fun foldl f z {hyps, hidden} = Tl.foldl f z hyps
    fun foldr f z {hyps, hidden} = Tl.foldr f z hyps

    fun snoc {hyps, hidden} x jdg =
      {hyps = Tl.snoc hyps x jdg,
       hidden = (x, Sym.name x) :: hidden}

    val empty = {hyps = Tl.empty, hidden = []}

    fun singleton x jdg = 
      {hyps = Tl.singleton x jdg,
       hidden = [(x, Sym.name x)]}

    fun isEmpty {hyps, hidden} = Tl.isEmpty hyps

    fun map f {hyps, hidden} =
      {hyps = Tl.map f hyps,
       hidden = hidden}

    fun modify x f {hyps, hidden} =
      {hyps = Tl.modify x f hyps,
       hidden = hidden}

    fun truncateFrom {hyps, hidden} x =
      {hyps = Tl.truncateFrom hyps x,
       hidden = hidden}

    (* The telescope lib should be redesigned to make the following helper functions easier.
     * At least the calling convention can be more consistent. *)

    fun substAfter (z, term) {hyps, hidden} = 
      {hyps = Tl.modifyAfter z (AJ.map (Tm.substVar (term, z))) hyps,
       hidden = hidden}

    fun splice {hyps, hidden} x (H : hyps) =
      {hyps = Tl.splice hyps x (#hyps H),
       hidden = #hidden H @ hidden}

    fun interposeAfter (z, H' : hyps) {hyps, hidden} =
      {hyps = Tl.interposeAfter hyps z (#hyps H'),
       hidden = #hidden H' @ hidden}

    fun interposeThenSubstAfter (z, H' : hyps, term) {hyps, hidden} =
      {hyps = Tl.interposeAfter (Tl.modifyAfter z (AJ.map (Tm.substVar (term, z))) hyps) z (#hyps H'),
       hidden = #hidden H' @ hidden}

    fun pretty (H : hyps) : TermPrinter.env * Fpp.doc =
      let
        val ppProvenience = 
          fn NONE => Fpp.empty
           | SOME str => Fpp.seq [Fpp.char #"/", Fpp.text str]

        fun ppHidden (i, nm) =
          Fpp.seq
            [Fpp.text "_", Fpp.text (Int.toString i),
             ppProvenience nm]

        val (hiddenNames, _) =
          List.foldr 
            (fn ((x, nm), (rho, n)) => (Var.Ctx.insert rho x (ppHidden (n, nm)), n + 1))
            (Var.Ctx.empty, 0)
            (#hidden H)

        val varNames = 
          Tl.foldl
            (fn (x, _, names) => Var.Ctx.insertMerge names x (TermPrinter.ppVar x) (fn d => d))
            hiddenNames
            (#hyps H)

        val env : TermPrinter.env =
          {var = varNames,
           meta = Metavar.Ctx.empty,
           level = 0}

        fun ppHyp x = TermPrinter.ppVar' env x
      in
        (env, Fpp.vsep (foldr (fn (x, a, r) => Fpp.hsep [ppHyp x, Fpp.Atomic.colon, AJ.pretty' env a] :: r) [] H))
      end

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

      fun relabel {hyps, hidden} rho = 
        {hyps = relabelTl hyps rho,
         hidden = List.map (fn (x, nm) => (Var.Ctx.lookup rho x handle _ => x, nm)) hidden}
      
      fun *** (f, g) (x, y) = (f x, g y)
      infix 5 ***

      fun eq (H1 : hyps, H2 : hyps) =
        telescopeEq (#hyps H1, #hyps H2)
          andalso ListPair.allEq (Sym.eq o #1 *** #1) (#hidden H1, #hidden H2) handle _ => false
    end
  end

  datatype jdg =
     (* sequents / formal hypothetical judgment *)
     >> of hyps * atjdg

  infix >>

  fun map f =
    fn H >> catjdg => Hyps.map (AJ.map f) H >> AJ.map f catjdg

  fun relabel srho =
    fn H >> catjdg => Hyps.relabel H srho >> AJ.map (Tm.renameVars srho) catjdg

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
         let
           val (env, doc) = Hyps.pretty H
         in         
           ruleSep (doc, AJ.pretty' env atjdg)
         end

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


  fun push xs jdg =
    let
      fun clone x = (Sym.new (), Sym.name x)

      val {hyps = hyps, ...} >> _ = jdg

      fun hypIsActive x = 
        case Tl.find hyps x of
           SOME _ => true
         | NONE => false

      val (xs', rho) =
        List.foldr
          (fn (x, (xs, rho)) =>
            if hypIsActive x then
              let val x' = clone x in (x' :: xs, Sym.Ctx.insert rho x (#1 x')) end
            else
              (xs, rho))
          ([], Sym.Ctx.empty)
          xs
      val {hyps, hidden} >> ajdg = relabel rho jdg
    in
      {hyps = hyps, hidden = xs' @ hidden} >> ajdg
    end

  structure E = RedPrlError
  fun @@ (f, x) = f x infixr @@

  fun popAs xs' jdg =
    let
      val H as {hidden, ...} >> _ = jdg
      val n = List.length xs'
      val (xs, hidden') = (List.take (hidden,n), List.drop (hidden, n)) handle _ => E.raiseError @@ E.GENERIC [Fpp.text "Sequent.popAs: out of hiddens"]
      val rho = ListPair.foldl (fn ((x, _), x', rho) => Sym.Ctx.insert rho x x') Sym.Ctx.empty (xs, xs')
      val {hyps, ...} >> ajdg = relabel rho H
    in
      {hidden = hidden', hyps = hyps} >> ajdg
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
