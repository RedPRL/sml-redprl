signature SYNTH_RULES =
sig
  val CheckToSynth : RefinerKit.ntactic
  val SynthEqIntro : RefinerKit.ntactic

  (* H >> R syn ~> univ(i)
   *   H >> R type ~> i
   *)
  val SynthType : RefinerKit.ntactic
end
