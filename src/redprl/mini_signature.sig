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

  (* For Favonia - jms *)
  val dataDeclInfo : sign -> opid -> unit
end
