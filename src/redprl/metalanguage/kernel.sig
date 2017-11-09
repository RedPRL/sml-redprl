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

  val subst : proof * meta -> proof -> proof
end