functor Sequent (structure CJ : CATEGORICAL_JUDGMENT
                                  where type 'a Tm.O.t = 'a RedPrlOperator.t
                                  where type Tm.O.Ar.Vl.S.t = RedPrlSort.t
                                  where type 'a Tm.O.P.term = 'a RedPrlParameterTerm.t
                                  where type Tm.Sym.t = Sym.t
                                  where type Tm.Var.t = Sym.t
                 sharing type CJ.Tm.Sym.Ctx.dict = CJ.Tm.Var.Ctx.dict) : SEQUENT =
struct
  structure CJ = CJ
  structure Tm = CJ.Tm

  type var = Tm.variable
  type sym = Tm.symbol
  type psort = Tm.psort
  type sort = Tm.sort
  type operator = Tm.operator
  type param = Tm.param
  type hyp = sym
  type abt = CJ.Tm.abt
  type label = string

  structure Hyps : TELESCOPE = Telescope (Sym)
  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of ((sym * psort) list * (sym, 'a) CJ.jdg ctx) * (sym, 'a) CJ.jdg
   | MATCH of operator * int * 'a * param list * 'a list
   | MATCH_RECORD of label * 'a

  infix >>

  fun map f =
    fn (I, H) >> catjdg => (I, Hyps.map (CJ.map_ f) H) >> CJ.map_ f catjdg
     | MATCH (th, k, a, ps, ms) => MATCH (th, k, f a, ps, List.map f ms)
     | MATCH_RECORD (lbl, tm) => MATCH_RECORD (lbl, f tm)

  fun renameHypsInTerm srho =
    Tm.substSymenv (Tm.Sym.Ctx.map Tm.O.P.VAR srho)
      o Tm.renameVars srho

  local
    open Hyps.ConsView
  in
    fun telescopeEq (t1, t2) =
      case (out t1, out t2) of
         (EMPTY, EMPTY) => true
       | (CONS (x, catjdg1, t1'), CONS (y, catjdg2, t2')) =>
           Tm.Sym.eq (x, y)
             andalso CJ.eq (catjdg1, catjdg2)
             andalso telescopeEq (t1', t2')
       | _ => false

    fun relabelHyps H srho =
      let
        val srho' = Tm.Sym.Ctx.map Tm.O.P.VAR srho
      in
        case out H of
           EMPTY => Hyps.empty
         | CONS (x, catjdg, Hx) =>
           let
             val catjdg' = CJ.map_ (Tm.substSymenv srho') catjdg
           in
             case Tm.Sym.Ctx.find srho x of
                 NONE => Hyps.cons x catjdg' (relabelHyps Hx srho)
               | SOME y => Hyps.cons y catjdg' (relabelHyps Hx srho)
           end
      end

  end

  fun relabel srho =
    fn (I, H) >> catjdg =>
       (List.map (fn (u, sigma) => (Tm.Sym.Ctx.lookup srho u handle _ => u, sigma)) I, relabelHyps H srho)
         >> CJ.map_ (renameHypsInTerm srho) catjdg
     | jdg => map (renameHypsInTerm srho) jdg

  structure P = CJ.Tm.O.P and PS = CJ.Tm.O.Ar.Vl.PS

  fun prettySyms syms =
    Fpp.collection
      (Fpp.char #"{")
      (Fpp.char #"}")
      (Fpp.Atomic.comma)
      (List.map (fn (u, sigma) => Fpp.hsep [Fpp.text (Sym.DebugShow.toString u), Fpp.Atomic.colon, Fpp.text (Tm.O.Ar.Vl.PS.toString sigma)]) syms)

  fun prettyHyps f : 'a ctx -> Fpp.doc =
    Fpp.vsep o Hyps.foldr (fn (x, a, r) => Fpp.hsep [Fpp.text (Tm.Sym.DebugShow.toString x), Fpp.Atomic.colon, f a] :: r) []

  fun pretty eq f : 'a jdg -> Fpp.doc =
    fn (I, H) >> catjdg =>
       Fpp.seq
         [case I of [] => Fpp.empty | _ => Fpp.seq [prettySyms I, Fpp.newline],
          if Hyps.isEmpty H then Fpp.empty else Fpp.seq [prettyHyps (CJ.pretty eq f) H, Fpp.newline],
          Fpp.hsep [Fpp.text ">>", CJ.pretty eq f catjdg]]
     | MATCH (th, k, a, _, _) => Fpp.hsep [f a, Fpp.text "match", Fpp.text (Tm.O.toString Tm.Sym.DebugShow.toString th), Fpp.text "@", Fpp.text (Int.toString k)]
     | MATCH_RECORD (lbl, a) => Fpp.hsep [f a, Fpp.text "match_record", Fpp.text lbl]
  fun pretty' f = pretty (fn _ => false) f

  val rec eq =
    fn ((I1, H1) >> catjdg1, (I2, H2) >> catjdg2) =>
       (let
         fun unifyPsorts (sigma1, sigma2) =
           if PS.eq (sigma1, sigma2) then sigma1 else
             raise Fail "psort mismatch in Sequent.eq"

         val I = ListPair.mapEq (fn ((_, sigma1), (_, sigma2)) => (Sym.new (), unifyPsorts (sigma1, sigma2))) (I1, I2)
         val srho1 = ListPair.foldr (fn ((u1, _), (u, _), rho) => Tm.Sym.Ctx.insert rho u1 (P.ret u)) Tm.Sym.Ctx.empty (I1, I)
         val srho2 = ListPair.foldr (fn ((u2, _), (u, _), rho) => Tm.Sym.Ctx.insert rho u2 (P.ret u)) Tm.Sym.Ctx.empty (I2, I)

         val xs1 = Hyps.foldr (fn (x, _, xs) => x :: xs) [] H1
         val xs2 = Hyps.foldr (fn (x, _, xs) => x :: xs) [] H2
         val xs = ListPair.mapEq (fn _ => Sym.new ()) (xs1, xs2)
         val xrho1 = ListPair.foldr (fn (x1, x, rho) => Tm.Sym.Ctx.insert rho x1 x) Tm.Sym.Ctx.empty (xs1, xs)
         val xrho2 = ListPair.foldr (fn (x2, x, rho) => Tm.Sym.Ctx.insert rho x2 x) Tm.Sym.Ctx.empty (xs2, xs)

         val H1' = Hyps.map (CJ.map_ (CJ.Tm.substSymenv srho1)) (relabelHyps H1 xrho1)
         val H2' = Hyps.map (CJ.map_ (CJ.Tm.substSymenv srho2)) (relabelHyps H2 xrho2)
         val catjdg1' = CJ.map_ (CJ.Tm.substSymenv srho1 o renameHypsInTerm xrho1) catjdg1
         val catjdg2' = CJ.map_ (CJ.Tm.substSymenv srho2 o renameHypsInTerm xrho2) catjdg2
       in
         telescopeEq (H1', H2')
           andalso CJ.eq (catjdg1', catjdg2')
       end
       handle _ => false)
     | (MATCH (th1, k1, a1, ps1, ms1), MATCH (th2, k2, a2, ps2, ms2)) =>
          CJ.Tm.O.eq CJ.Tm.Sym.eq (th1, th2)
            andalso k1 = k2
            andalso Tm.eq (a1, a2)
            andalso ListPair.allEq (Tm.O.P.eq Tm.Sym.eq) (ps1, ps2)
            andalso ListPair.allEq Tm.eq (ms1, ms2)
     | (MATCH_RECORD (lbl1, a1), MATCH_RECORD (lbl2, a2)) =>
          lbl1 = lbl2 andalso Tm.eq (a1, a2)
     | _ => false
end
