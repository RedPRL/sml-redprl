functor Sequent (CJ : CATEGORICAL_JUDGMENT) : SEQUENT =
struct
  structure CJ = CJ
  structure Tm = CJ.Tm

  type var = Tm.variable
  type sym = Tm.symbol
  type psort = Tm.psort
  type sort = Tm.sort
  type operator = Tm.operator
  type hyp = sym

  structure Hyps : TELESCOPE = Telescope (Tm.Sym)
  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a CJ.jdg ctx * 'a CJ.jdg
   | |> of ((sym * psort) list * (var * sort) list) * 'a jdg
   | MATCH of operator * int * 'a

  infix >> |>

  fun map f =
    fn H >> catjdg => Hyps.map (CJ.map f) H >> CJ.map f catjdg
     | (U,G) |> jdg => (U,G) |> map f jdg
     | MATCH (th, k, a) => MATCH (th, k, f a)

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

  val rec eq =
    fn (H1 >> catjdg1, H2 >> catjdg2) =>
          telescopeEq (H1, H2)
            andalso CJ.eq (catjdg1, catjdg2)
     | ((U1,G1) |> jdg1, (U2,G2) |> jdg2) =>
          ListPair.allEq (fn ((u1, sort1), (u2, sort2)) => CJ.Tm.Sym.eq (u1, u2) andalso CJ.Tm.O.Ar.Vl.PS.eq (sort1, sort2)) (U1, U2)
            andalso ListPair.allEq (fn ((x1, sort1), (x2, sort2)) => CJ.Tm.Var.eq (x1, x2) andalso CJ.Tm.O.Ar.Vl.S.eq (sort1, sort2)) (G1, G2)
            andalso eq (jdg1, jdg2)
     | (MATCH (th1, k1, a1), MATCH (th2, k2, a2)) =>
          CJ.Tm.O.eq CJ.Tm.Sym.eq (th1, th2)
            andalso k1 = k2
            andalso Tm.eq (a1, a2)
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
       | MATCH (th, k, a) => concat [text (f a), text " match ", text (Tm.O.toString Tm.Sym.toString th), text " @ ", int k]
       | (U, G) |> jdg => pretty f jdg
  end

  fun toString f = PP.toString 80 true o pretty f
end
