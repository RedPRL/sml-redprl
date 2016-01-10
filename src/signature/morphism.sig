signature SIGNATURE_MORPHISM =
sig
  structure S1 : SIGNATURE
  structure S2 : SIGNATURE

  val decl : S2.sign -> S1.decl -> S2.decl
end

