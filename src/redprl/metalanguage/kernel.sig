signature KERNEL =
sig
  type proof
  type jdg = Lcf.jdg
  type meta = Lcf.L.var
  type name = RedPrlAbt.variable
  type rule = string

  val concl : proof -> jdg

  val init : jdg -> proof
  val rule : jdg -> rule * name list -> proof

  type action
  val subst : proof * meta -> action
  val apply: action list * proof -> action
end