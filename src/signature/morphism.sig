(* A signature morphism is the core part of a translation between two
 * phases of a signature. Each portion of elaboration boils down to a
 * different implementation of SIGNATURE_MORPHISM
 *)
signature SIGNATURE_MORPHISM =
sig
  (* Source *)
  structure S1 : SIGNATURE
  (* Target *)
  structure S2 : SIGNATURE

  (* In order to implement this transformation this is the
   * only required function to implement. It describes how to
   * elaborate one sorce declaration given all the rest of the
   * previously elaborated declarations. See TransportSignature
   * for how this is elaborated into a map between two full
   * signatures.
   *)
  val decl : S2.sign -> S1.decl -> S2.decl
end
