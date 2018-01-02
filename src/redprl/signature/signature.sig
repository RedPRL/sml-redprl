signature MINI_SIGNATURE =
sig
  type opid = RedPrlOpData.opid
  type abt = RedPrlAbt.abt
  
  type sign
  val theoremSpec : sign -> opid -> abt RedPrlAbt.bview list -> AtomicJudgment.jdg
  val unfoldOpid : sign -> opid -> abt RedPrlAbt.bview list -> abt

  val isTheorem : sign -> opid -> bool
end
