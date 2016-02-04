(* After all the binding structure has been resolved we have this
 * morhpism which validates that each [CUST] is actually valid. That is
 * that each [CUST (id, symbs, arity)] refers to an operator which
 *  - Exists in the signature before its occurence
 *  - Actually has the arity we claim it does
 * However beyond that this pass doesn't actually modify anything
 *
 * NOTE: This pass doesn't really comport with the formalized elaboration
 * semantics for signatures. This is because in our semantics, custom operators
 * don't carry around their arities. However, due to the way that the abstract
 * binding tree logical framework is implemented, we must specify our operators
 * statically, and so it is necessary for members of family of operators of
 * varying arity to carry their arities.
 *)
structure ValidationElab : SIGNATURE_ELAB =
struct
  structure S1 = AbtSignature
  structure S2 = AbtSignature

  open Abt
  infix $ \ $#


  structure Telescope = SymbolTelescope
  structure DefnMap = SplayDict(structure Key = Symbol)

  (* TODO: Should we standardize how we report these errors?
   * Do we only want to throw back the op name?
   *)
  exception InvalidCustomOper of S1.opid

  (* This is the main part of the transformation, it validates
   * that the data associated with a CUST operator is actually
   * what the definition says it is.
   *)
  fun validate map (OperatorData.CUST (opid, params, arity)) =
    let
      val {parameters, arguments, sort, definiens} =
        case DefnMap.find map opid of
            NONE => raise InvalidCustomOper opid
          | SOME x => S1.undef x
      val sorts = ListPair.zipEq (List.map #2 params, List.map #2 parameters)
      val () =
        if List.all Sort.eq sorts then () else raise InvalidCustomOper opid
      val expectedArity = (List.map #2 arguments, sort)
      val () =
        if Arity.eq (expectedArity, arity) then () else raise InvalidCustomOper opid
    in
      ()
    end
    | validate _ _ = () (* This may seem redundant but helps type inference *)

  (* This traverses a declaration and ensures that each operator
   * that occurs in the body is correct with respect to the signature
   * it appears in.
   *)
  fun checkDecl map =
    let
      fun go e =
        case #1 (Abt.infer e) of
            ` _ => ()
          | oper $ args => (validate map oper; List.app goAbs args)
          | _ $# (_, args) => List.app go args
      and goAbs (_ \ a) = go a
    in
      go o #definiens o S1.undef
    end

  (* This is just the straightforward extension of checkDecl to full
   * telescopes of signatures. It also correctly updates and propogates
   * the map through each call.
   *)
  fun transport sign =
    let
      fun go map sign =
        case Telescope.ConsView.out sign of
            Telescope.ConsView.Empty => ()
          | Telescope.ConsView.Cons (l, a, s) =>
            (checkDecl map a; go (DefnMap.insert map l a) s)
    in
      (* Note that since we're just validating the signature
       * at the end we just return the input
       *)
      go DefnMap.empty sign;
      sign
    end
end
