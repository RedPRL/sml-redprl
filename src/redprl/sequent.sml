functor Sequent (CJ : CATEGORICAL_JUDGMENT) : SEQUENT =
struct
  structure CJ = CJ
  structure Tm = CJ.Tm

  type var = Tm.variable
  type sym = Tm.symbol
  type psort = Tm.psort
  type sort = Tm.sort
  type hyp = sym

  structure Hyps : TELESCOPE = Telescope (Tm.Sym)

  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a ctx * 'a
   | |> of ((sym * psort) list * (var * sort) list) * 'a jdg

  infix >> |>

  fun map f =
    fn H >> catjdg => Hyps.map f H >> f catjdg
     | (U,G) |> jdg => (U,G) |> map f jdg

  structure PP = PrettyPrint

  local
    open PP
  in
    fun prettyHyps f : 'a ctx -> doc =
      Hyps.foldl
        (fn (x, a, r) => concat [r, text (Tm.Sym.toString x), text " : ", text (f a), line])
        empty

    fun pretty f : 'a jdg -> doc =
      fn H >> catjdg => concat [prettyHyps f H, text "\226\138\162 ", text (f catjdg)]
       | (U, G) |> jdg => pretty f jdg
  end

  fun toString f = PP.toString 80 o pretty f
end
