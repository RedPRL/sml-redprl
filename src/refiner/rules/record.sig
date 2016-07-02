signature RECORD_RULES =
sig
  val IsType : RefinerKit.ntactic
  val TypeEq : RefinerKit.ntactic
  val MemberEq : RefinerKit.ntactic
  val IntroRecord : RefinerKit.ntactic
  val IntroSingl : RefinerKit.ntactic
  val ProjSynth : RefinerKit.ntactic
end
