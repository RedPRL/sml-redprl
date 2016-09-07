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

  fun hypsToString f H =
    let
      open Hyps open ConsView
      val rec go =
        fn EMPTY => ""
         | CONS (x, a, tl) =>
             let
               val hyp = Tm.Sym.toString x ^ " : " ^ f a
             in
               hyp ^ (if isEmpty tl then " " else ", " ^ go (out tl))
             end
    in
      go (out H)
    end

  fun toString f =
    fn H >> catjdg => "{" ^ hypsToString f H ^ "\226\138\162 " ^ f catjdg ^ "}"
     | (U, G) |> jdg =>
        "{" ^ ListSpine.pretty (Tm.Sym.toString o #1) "," U ^ "}" ^
        "[" ^ ListSpine.pretty (Tm.Var.toString o #1) "," G ^ "] | " ^ toString f jdg
end

