signature ENSEMBLE_RULES =
sig
  val IsType : RefinerKit.ntactic
  val TypeEq : RefinerKit.ntactic
  val MemberEq : RefinerKit.ntactic
  val Intro : RefinerKit.ntactic
  val Elim : RefinerKit.symbol -> RefinerKit.ntactic
end
