signature CATEGORICAL_JUDGMENT =
sig
  datatype 'a jdg =
     EQ of ('a * 'a) * 'a
   | MEM of 'a * 'a
   | TRUE of 'a
   | SYNTH of 'a
   | CEQUIV of 'a * 'a

  val map : ('a -> 'b) -> 'a jdg -> 'b jdg

  type abt = RedPrlAbt.abt
  type sort = RedPrlAbt.sort

  (* What sort of term does the jdg synthesize? *)
  val synthesis : 'a jdg -> RedPrlAbt.sort

  val toAbt : abt jdg -> abt
  val fromAbt : abt -> abt jdg

  exception InvalidJudgment
end
