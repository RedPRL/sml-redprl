(* A signature morphism is the core part of a translation between two
 * phases of a signature. Each portion of elaboration boils down to a
 * different implementation of [SIGNATURE_MORPHISM]
 *)
signature SIGNATURE_MORPHISM =
sig
  (* Source elaboration phase *)
  structure S1 : SIGNATURE
  (* Target elaboration phase *)
  structure S2 : SIGNATURE

  (* In order to implement this transformation it suffices to
   * implement the following functions. See [TransportSignature]
   * for how these is extended into a map between two full
   * signatures. *)

  (* The operation [decl] shows how to elaborate one source declaration
   * given all the rest of the previously extended declarations. *)
  val decl : S2.sign -> S1.decl -> S2.decl

  (* The operation [opid] shows how to elaborate an operator id
   * from one phase into the next. *)
  val opid : S2.sign -> S1.opid -> S2.opid
end
