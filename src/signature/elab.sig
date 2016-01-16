(* A signature elaboration is a translation between two
 * phases of a signature. Each portion of elaboration comes down to
 * different implementation of [SIGNATURE_MORPHISM].
 *)
signature SIGNATURE_ELAB =
sig
  (* Source elaboration phase *)
  structure S1 : SIGNATURE
  (* Target elaboration phase *)
  structure S2 : SIGNATURE

  (* This is the actual transformation between [S1.sign] and [S2.sign] *)
  val transport : S1.sign -> S2.sign
end
