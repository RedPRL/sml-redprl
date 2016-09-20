signature SEQUENT =
sig
  structure CJ : CATEGORICAL_JUDGMENT

  type var = CJ.Tm.variable
  type sym = CJ.Tm.symbol
  type psort = CJ.Tm.psort
  type sort = CJ.Tm.sort
  type operator = CJ.Tm.operator
  type hyp = sym

  structure Hyps : TELESCOPE where type Label.t = hyp

  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a CJ.jdg ctx * 'a CJ.jdg
   | |> of ((sym * psort) list * (var * sort) list) * 'a jdg
   | MATCH of operator * int * 'a

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg

  val pretty : ('a -> string) -> 'a jdg -> PP.doc
  val toString : ('a -> string) -> 'a jdg -> string
end
