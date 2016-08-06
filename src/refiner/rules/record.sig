signature RECORD_RULES =
sig
  val IsType : RefinerKit.ntactic
  val TypeEq : RefinerKit.ntactic
  val MemberEq : RefinerKit.ntactic
  val Intro : RefinerKit.ntactic
  val ProjSynth : RefinerKit.ntactic
end
