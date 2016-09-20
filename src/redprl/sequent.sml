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
   (*
   | MATCH of operator * int * 'a
   *)

  infix >> |>

  fun map f =
    fn H >> catjdg => Hyps.map (CJ.map f) H >> CJ.map f catjdg
     | (U,G) |> jdg => (U,G) |> map f jdg
     (*
     | MATCH (th, k, a) => MATCH (th, k, f a)
     *)

  local
    open PP
  in
    fun prettyHyps f : 'a ctx -> doc =
      Hyps.foldl
        (fn (x, a, r) => concat [r, text (Tm.Sym.toString x), text " : ", f a, line])
        empty

    fun pretty f : 'a jdg -> doc =
      fn H >> catjdg => concat [prettyHyps (CJ.pretty f) H, text "\226\138\162 ", CJ.pretty f catjdg]
       (* | MATCH (th, k, a) => concat [*)
       | (U, G) |> jdg => pretty f jdg
  end

  fun toString f = PP.toString 80 true o pretty f
end
