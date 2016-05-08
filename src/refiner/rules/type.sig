(* rules for the [H >> P type] judgment, which synthesizes a level. *)
signature TYPE_RULES =
sig
  val Intro : RefinerKit.ntactic

  (* H >> A type ~> i
   *   H >> A syn ~> Univ(i)
   *)
  val Synth : RefinerKit.ntactic
end
