(* This is what is needed to bootstrap the refiner, and thence the tactic elaborator. This
   enables rules that depend on the definitions of theorems and other operators.

   TODO: rename to something more sensible
 *)
signature MINI_SIGNATURE =
sig
  type opid = RedPrlOpData.opid
  type abt = RedPrlAbt.abt

  type sign
  val theoremSpec : sign -> opid -> abt RedPrlAbt.bview list -> AtomicJudgment.jdg
  val unfoldOpid : sign -> opid -> abt RedPrlAbt.bview list -> abt

  val isTheorem : sign -> opid -> bool

  (* TODO explain the following function to someone other than favonia. *)
  val dataDeclInfo : sign -> opid -> abt RedPrlAbt.bview list ->
     abt RedPrlAbt.bview list * (abt * InductiveSpec.precomputed_valences) * abt list
end
