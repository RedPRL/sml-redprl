signature SEQUENT =
sig
  type var = RedPrlAbt.variable
  type sym = RedPrlAbt.symbol
  type psort = RedPrlAbt.psort
  type sort = RedPrlAbt.sort
  type hyp = sym

  structure Hyps : TELESCOPE where type Label.t = hyp

  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of 'a ctx * 'a
   | |> of ((sym * psort) list * (var * sort) list) * 'a jdg

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg
  val toString : ('a -> string) -> 'a jdg -> string
end
