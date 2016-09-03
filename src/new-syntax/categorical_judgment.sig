signature CATEGORICAL_JUDGMENT =
sig
  datatype 'a judgment =
     EQ of ('a * 'a) * 'a
   | MEM of 'a * 'a
   | TRUE of 'a
   | SYNTH of 'a
   | CEQUIV of 'a * 'a

  val map : ('a -> 'b) -> 'a judgment -> 'b judgment

  type abt = RedPrlAbt.abt
  type sort = RedPrlAbt.sort

  (* What sort of term does the judgment synthesize? *)
  val synthesis : 'a judgment -> RedPrlAbt.sort

  val into : abt judgment -> abt
  val out : abt -> abt judgment

  exception InvalidJudgment
end
