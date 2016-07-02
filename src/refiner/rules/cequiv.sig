signature CEQUIV_RULES =
sig
  val IsType
    : RefinerKit.ntactic

  val TypeEq
    : RefinerKit.ntactic

  val CStep
    : AbtSignature.sign
    -> int
    -> RefinerKit.ntactic

  val CSym
    : RefinerKit.ntactic

  val CEval
    : AbtSignature.sign
    -> RefinerKit.ntactic

  val MemberEq
    : RefinerKit.ntactic

  val Eta
    : RefinerKit.symbol
    -> RefinerKit.ntactic

end
