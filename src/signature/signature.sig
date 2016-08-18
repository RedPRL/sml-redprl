(* A signature, which is a collection of declarations, is the core building
 * block of a RedPRL development.
 *
 * An implementation of [SIGNATURE] is a particular phase of signature
 * elaboration; one phase might have, for instance, many forms of declaration,
 * some of which are elaborated into a single form of declaration in another
 * phase. See [SIGNATURE_MORPHISM] for the specification of an elaboration
 * from one signature to another; given a [SIGNATURE_MORPHISM], the
 * [TransportSignature] functor can be used to perform the elaboration of
 * a signature from one phase to the other.
 *)

signature SIGNATURE =
sig
  type opid
  type decl

  structure Telescope : TELESCOPE where type Label.t = opid

  (* A signature / [sign] is a telescope of declarations. *)
  type sign = (decl * Pos.t option) Telescope.telescope
end
