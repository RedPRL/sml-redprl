signature SEQUENT =
sig
  structure CJ : CATEGORICAL_JUDGMENT

  type var = CJ.Tm.variable
  type sym = CJ.Tm.symbol
  type psort = CJ.Tm.psort
  type sort = CJ.Tm.sort
  type operator = CJ.Tm.operator
  type param = CJ.Tm.param
  type hyp = sym
  type abt = CJ.Tm.abt
  type label = string

  structure Hyps : TELESCOPE where type Label.t = hyp

  type 'a ctx = 'a Hyps.telescope

  datatype 'a jdg =
     >> of ((sym * psort) list * 'a CJ.jdg ctx) * 'a CJ.jdg     (* sequents / formal hypothetical judgment *)
   | MATCH of operator * int * 'a * param list * 'a list        (* unify a term w/ a head operator and extract the kth subterm *)
   | MATCH_RECORD of label * 'a                                 (* unify a term w/ RECORD and extract the subterm of the label *)
   | DIM_SUBST of 'a * sym * 'a                                 (* substitute a dimension *reference* for a symbol in a term *)

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg

  val pretty : ('a * 'a -> bool) -> ('a -> Fpp.doc) -> 'a jdg -> Fpp.doc
  val pretty' : ('a -> Fpp.doc) -> 'a jdg -> Fpp.doc

  val eq : CJ.Tm.abt jdg * CJ.Tm.abt jdg -> bool

  val relabel : hyp CJ.Tm.Sym.Ctx.dict -> abt jdg -> abt jdg
end
