signature SPECIES_RULES =
sig
  val TypeEq : RefinerKit.ntactic
  val MemberEq : RefinerKit.ntactic
  val Intro : RefinerKit.ntactic
  val Elim : RefinerKit.symbol -> RefinerKit.ntactic
end
