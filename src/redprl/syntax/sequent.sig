structure RedPrlSequentData =
struct
  type catjdg = RedPrlAtomicJudgment.jdg
  type abt = RedPrlAbt.abt

  structure Hyps : TELESCOPE = Telescope (Sym)
  type 'a ctx = 'a Hyps.telescope

  type label = string

  datatype jdg =
     (* sequents / formal hypothetical judgment *)
     >> of catjdg ctx * catjdg
     (* unify a term w/ a head operator and extract the kth subterm *)
   | MATCH of RedPrlAbt.operator * int * abt * abt list
     (* unify a term w/ RECORD and extract the type of the label;
      * the third argument is the tuple. *)
   | MATCH_RECORD of label * abt * abt
end

signature SEQUENT =
sig
  datatype atjdg = datatype RedPrlAtomicJudgment.jdg
  datatype jdg = datatype RedPrlSequentData.jdg
  type 'a ctx = 'a RedPrlSequentData.ctx

  type abt = RedPrlAbt.abt

  val map : (abt -> abt) -> jdg -> jdg

  (* specialized to abt *)
  val pretty : jdg -> Fpp.doc
  val eq : jdg * jdg -> bool
  val relabel : Sym.t Sym.Ctx.dict -> jdg -> jdg

  val lookupSelector : Sym.t Selector.t -> atjdg ctx * atjdg -> atjdg
  val mapSelector : Sym.t Selector.t -> (atjdg -> atjdg) -> atjdg ctx * atjdg -> atjdg ctx * atjdg
  val multiMapSelector : Sym.t Selector.t list -> (atjdg -> atjdg) -> atjdg ctx * atjdg -> atjdg ctx * atjdg

  (* TODO: I don't like this function. *)
  val truncateFrom : Sym.t Selector.t -> atjdg ctx -> atjdg ctx
end
