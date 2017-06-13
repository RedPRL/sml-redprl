functor Sequent (structure CJ : CATEGORICAL_JUDGMENT
                                  where type 'a Tm.O.Ar.Vl.Sp.t = 'a list
                                  where type 'a Tm.O.t = 'a RedPrlOperator.t
                                  where type Tm.O.Ar.Vl.S.t = RedPrlSort.t
                                  where type 'a Tm.O.P.term = 'a RedPrlParameterTerm.t
                 sharing type CJ.Tm.Sym.t = CJ.Tm.Var.t) : SEQUENT =
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

  structure Hyps : TELESCOPE = Telescope (Tm.Sym)
  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a CJ.jdg ctx * 'a CJ.jdg
   | MATCH of operator * int * 'a * param list * 'a list

  infix >>

  fun map f =
    fn H >> catjdg => Hyps.map (CJ.map f) H >> CJ.map f catjdg
     | MATCH (th, k, a, ps, ms) => MATCH (th, k, f a, ps, List.map f ms)

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
  end

  val renameHypsInTerm =
    Tm.substSymenv o Tm.Sym.Ctx.map Tm.O.P.VAR

  fun relabelHyp (u, v) H =
    let
      val jdg = Hyps.lookup H u
      val H' = Hyps.interposeAfter H u (Hyps.singleton v jdg)
    in
      Hyps.remove u H'
    end
    handle _ => H

  fun relabelHyps H srho = 
    Tm.Sym.Ctx.foldl 
      (fn (x, y, H) => relabelHyp (x, y) H)
      H
      srho

  fun relabel srho = 
    fn H >> catjdg => relabelHyps H srho >> CJ.map (renameHypsInTerm srho) catjdg
     | jdg => map (renameHypsInTerm srho) jdg

  val rec eq =
    fn (H1 >> catjdg1, H2 >> catjdg2) =>
          telescopeEq (H1, H2)
            andalso CJ.eq (catjdg1, catjdg2)
     | (MATCH (th1, k1, a1, ps1, ms1), MATCH (th2, k2, a2, ps2, ms2)) =>
          CJ.Tm.O.eq CJ.Tm.Sym.eq (th1, th2)
            andalso k1 = k2
            andalso Tm.eq (a1, a2)
            andalso ListPair.allEq (Tm.O.P.eq Tm.Sym.eq) (ps1, ps2)
            andalso ListPair.allEq Tm.eq (ms1, ms2)
     | _ => false

  local
    open PP
  in
    fun prettyHyps f : 'a ctx -> doc =
      Hyps.foldl
        (fn (x, a, r) => concat [r, text (Tm.Sym.toString x), text " : ", f a, line])
        empty

    fun pretty f : 'a jdg -> doc =
      fn H >> catjdg => concat [prettyHyps (CJ.pretty f) H, text "\226\138\162 ", CJ.pretty f catjdg]
       | MATCH (th, k, a, _, _) => concat [text (f a), text " match ", text (Tm.O.toString Tm.Sym.toString th), text " @ ", int k]
  end

  fun toString f = PP.toString 80 true o pretty f
end
