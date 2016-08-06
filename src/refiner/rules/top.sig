signature TOP_RULES =
sig
  val IsType : RefinerKit.ntactic
  val TypeEq : RefinerKit.ntactic
  val MemberEq : RefinerKit.ntactic

  val IntroTrivial : RefinerKit.ntactic
end
