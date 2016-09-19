signature SEQUENT =
sig
  structure CJ : CATEGORICAL_JUDGMENT

  type var = CJ.Tm.variable
  type sym = CJ.Tm.symbol
  type psort = CJ.Tm.psort
  type sort = CJ.Tm.sort
  type hyp = sym

  structure Hyps : TELESCOPE where type Label.t = hyp

  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a ctx * 'a
   | |> of ((sym * psort) list * (var * sort) list) * 'a jdg

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg

  val pretty : ('a -> string) -> 'a jdg -> PrettyPrint.doc
  val toString : ('a -> string) -> 'a jdg -> string
end
