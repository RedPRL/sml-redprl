structure RedPrlSequentData =
struct
  (* polymorphism is useful for preventing bugs *)
  type 'a catjdg = (Sym.t, 'a) RedPrlCategoricalJudgment.jdg'

  structure Hyps : TELESCOPE = Telescope (Sym)
  type 'a ctx = 'a Hyps.telescope

  type label = string

  (* polymorphism is useful for preventing bugs *)
  datatype 'a jdg' =
     (* sequents / formal hypothetical judgment *)
     >> of ((Sym.t * RedPrlAbt.psort) list * 'a catjdg ctx) * 'a catjdg
     (* unify a term w/ a head operator and extract the kth subterm *)
   | MATCH of RedPrlAbt.operator * int * 'a * RedPrlAbt.param list * 'a list
     (* unify a term w/ RECORD and extract the subterm of the label *)
   | MATCH_RECORD of label * 'a
end

signature SEQUENT =
sig
  datatype jdg' = datatype RedPrlSequentData.jdg'
  val map : ('a -> 'b) -> 'a jdg' -> 'b jdg'

  val pretty' : ('a -> Fpp.doc) -> ('a * 'a -> bool) -> 'a jdg' -> Fpp.doc

  (* specialized to abt *)
  type jdg = RedPrlAbt.abt jdg'
  val pretty : jdg -> Fpp.doc
  val eq : jdg * jdg -> bool
  val relabel : Sym.t Sym.Ctx.dict -> jdg -> jdg
end
