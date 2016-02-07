signature SQUASH_RULES =
sig
  val TypeEq : RefinerKit.ntactic
  val Intro : RefinerKit.ntactic
  val Unhide : RefinerKit.symbol -> RefinerKit.ntactic
end
