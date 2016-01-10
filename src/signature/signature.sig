signature SIGNATURE =
sig
  type decl

  (* A signature / [sign] is a telescope of declarations. *)
  type sign = decl StringTelescope.telescope
end
