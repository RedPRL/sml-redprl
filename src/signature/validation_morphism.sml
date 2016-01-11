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
structure ValidationMorphism : SIGNATURE_MORPHISM =
struct
  structure S1 = AbtSignature
  structure S2 = AbtSignature

  open Abt
  infix $ \ $#


  structure Telescope = SymbolTelescope

  structure DefnMap = SplayDict(structure Key = struct open Symbol; open Eq end)
  type map = S1.decl DefnMap.dict
  (* TODO: Should we standardize how we report these errors?
   * Do we only want to throw back the op name?
   *)
  exception InvalidCustomOper of S1.opid

  (* Given a signature turn it into an efficient random access
   * map for looking up information about the definition
   *)
  fun buildDefnMap sign =
    let
      fun go map sign =
          case Telescope.ConsView.out sign of
              Telescope.ConsView.Empty => map
            | Telescope.ConsView.Cons (l, a, r) =>
              go (DefnMap.insert map l a) r
    in
      go DefnMap.empty sign
    end

  fun validate map (OperatorData.CUST (opid, params, arity)) =
    let
      val {parameters, arguments, sort, definiens} =
        case DefnMap.find map opid of
            NONE => raise InvalidCustomOper opid
          | SOME x => S1.undef x
      val sorts = ListPair.zipEq (List.map #2 params, List.map #2 parameters)
      val () =
        if List.all Sort.Eq.eq sorts then () else raise InvalidCustomOper opid
      val expectedArity = (List.map #2 arguments, sort)
      val () =
        if Arity.Eq.eq (expectedArity, arity) then () else raise InvalidCustomOper opid
    in
      ()
    end
    | validate _ _ = () (* This may seem redundant but helps type inference *)

  (* TODO: This is inefficient because we rebuild the dict
   * on every call to [decl] even though we should really only
   * need to build it once. This means we are O(n^2) not
   * O(n) directly.
   *
   * Suggestion: make this pass *not a morphism* and instead define
   * transport
   *)
  fun decl prior decl =
    let
      val map = buildDefnMap prior

      fun go e =
        case #1 (Abt.infer e) of
            ` _ => ()
          | oper $ args => (validate map oper; List.app goAbs args)
          | _ $# (_, args) => List.app go args
      and goAbs (_ \ a) = go a
    in
      go (#definiens (S1.undef decl)); decl
    end

  (* Since we're not transforming stuff there's no work to be done here *)
  fun opid _ i = i
end
