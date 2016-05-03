(* rules for the [H >> P type] judgment, which synthesizes a level. *)
signature TYPE_RULES =
sig
  val Intro : RefinerKit.ntactic
  val Synth : RefinerKit.ntactic
end
