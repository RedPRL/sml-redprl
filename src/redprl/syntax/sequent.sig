signature SEQUENT =
sig
  datatype atjdg = datatype AtomicJudgment.jdg
  type abt = RedPrlAbt.abt
  type variable = RedPrlAbt.variable

  type hyps

  datatype jdg =
     (* sequents / formal hypothetical judgment *)
     >> of hyps * atjdg

  val map : (abt -> abt) -> jdg -> jdg

  (* specialized to abt *)
  val pretty : jdg -> Fpp.doc
  val eq : jdg * jdg -> bool
  val relabel : Sym.t Sym.Ctx.dict -> jdg -> jdg

  structure Hyps : 
  sig
    val empty : hyps
    val isEmpty : hyps -> bool
    val snoc : hyps -> variable -> atjdg -> hyps
    val foldr : (variable * atjdg * 'b -> 'b) -> 'b -> hyps -> 'b
    val foldl : (variable * atjdg * 'b -> 'b) -> 'b -> hyps -> 'b    
    val toList : hyps -> abt list  
    val lookup : hyps -> variable -> atjdg
    val substAfter : variable * abt -> hyps -> hyps
    val remove : variable -> hyps -> hyps
    val splice : hyps -> variable -> hyps -> hyps
    val singleton : variable -> atjdg -> hyps
    val map : (atjdg -> atjdg) -> (hyps -> hyps)
    val interposeAfter : variable * hyps -> hyps -> hyps
    val interposeThenSubstAfter : variable * hyps * abt -> hyps -> hyps
    val modifyAfter : variable -> (atjdg -> atjdg) -> hyps -> hyps
  end

  val lookupSelector : Sym.t Selector.t -> hyps * atjdg -> atjdg
  val mapSelector : Sym.t Selector.t -> (atjdg -> atjdg) -> hyps * atjdg -> hyps * atjdg
  val multiMapSelector : Sym.t Selector.t list -> (atjdg -> atjdg) -> hyps * atjdg -> hyps * atjdg

  (* TODO: I don't like this function. *)
  val truncateFrom : Sym.t Selector.t -> hyps -> hyps


  val push : variable list -> jdg -> jdg
  val popAs : variable list -> jdg -> jdg
end
