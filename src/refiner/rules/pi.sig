signature PI_RULES =
sig
  val TypeEq : RefinerKit.ntactic
  val MemberEq : RefinerKit.ntactic
  val ElimEq : RefinerKit.ntactic

  val Intro : RefinerKit.ntactic
  val Elim : RefinerKit.symbol -> RefinerKit.ntactic
  val Ext : RefinerKit.ntactic
end
