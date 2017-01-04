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
     >> of 'a CJ.jdg ctx * 'a CJ.jdg                            (* sequents / formal hypothetical judgment *)
   | MATCH of operator * int * 'a                               (* unify a term w/ a head operator and extract the kth subterm *)

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg

  val pretty : ('a -> string) -> 'a jdg -> PP.doc
  val toString : ('a -> string) -> 'a jdg -> string

  val eq : CJ.Tm.abt jdg * CJ.Tm.abt jdg -> bool
end
