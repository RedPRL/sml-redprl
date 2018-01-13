signature SEQUENT =
sig
  datatype atjdg = datatype AtomicJudgment.jdg

  type hyps

  datatype jdg =
     (* sequents / formal hypothetical judgment *)
     >> of hyps * atjdg
     (* unify a term w/ a head operator and extract the kth subterm *)
   | MATCH of RedPrlAbt.operator * int * Tm.abt * Tm.abt list
     (* unify a term w/ RECORD and extract the type of the label;
      * the third argument is the tuple. *)
   | MATCH_RECORD of string * Tm.abt * Tm.abt

  type abt = Tm.abt

  val map : (abt -> abt) -> jdg -> jdg

  (* specialized to abt *)
  val pretty : jdg -> Fpp.doc
  val eq : jdg * jdg -> bool
  val relabel : Sym.t Sym.Ctx.dict -> jdg -> jdg

  structure Hyps : 
  sig
    val empty : hyps
    val snoc : hyps -> Tm.variable -> atjdg -> hyps
    val foldr : (Tm.variable * atjdg * 'b -> 'b) -> 'b -> hyps -> 'b
    val foldl : (Tm.variable * atjdg * 'b -> 'b) -> 'b -> hyps -> 'b    
    val toList : hyps -> Tm.abt list  
    val lookup : hyps -> Tm.variable -> atjdg
    val substAfter : Tm.variable * Tm.abt -> hyps -> hyps
    val remove : Tm.variable -> hyps -> hyps
    val interposeAfter : Tm.variable * hyps -> hyps -> hyps
    val interposeThenSubstAfter : Tm.variable * hyps * Tm.abt -> hyps -> hyps
    val splice : hyps -> Tm.variable -> hyps -> hyps
    val singleton : Tm.variable -> atjdg -> hyps
    val modifyAfter : Tm.variable -> (atjdg -> atjdg) -> hyps -> hyps
  end

  val lookupSelector : Sym.t Selector.t -> hyps * atjdg -> atjdg
  val mapSelector : Sym.t Selector.t -> (atjdg -> atjdg) -> hyps * atjdg -> hyps * atjdg
  val multiMapSelector : Sym.t Selector.t list -> (atjdg -> atjdg) -> hyps * atjdg -> hyps * atjdg

  (* TODO: I don't like this function. *)
  val truncateFrom : Sym.t Selector.t -> hyps -> hyps
end
