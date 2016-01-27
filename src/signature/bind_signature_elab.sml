(* This pass takes a signature of AST terms and assigns identity to their
 * symbols and variables. *)
structure BindSignatureElab : SIGNATURE_ELAB =
struct
  structure S1 = AstSignature
  structure S2 = AbtSignature

  open AstSignatureDecl

  fun metacontext xs =
    case xs of
         [] => Metacontext.empty
       | d :: xs => Metacontext.extend (metacontext xs) d

  (* Given a AST declaration, this resolves its binding structure
   * in the context of the signature before it (given by [opidTable]).
   *)
  fun bindDecl opidTable sign (DEF {parameters, arguments, sort, definiens}) =
    let
      val (localNames, sorts) = ListPair.unzip parameters
      val localSymbols = List.map Symbol.named localNames
      val parameters' = ListPair.zipEq (localSymbols, sorts)

      local
        open AstToAbt
        val upsilon = NameEnv.fromList (opidTable @ ListPair.zipEq (localNames, localSymbols))
        val gamma = NameEnv.fromList []
        val mctx = metacontext arguments
      in
        val definiens' = convertOpen mctx (upsilon, gamma) (definiens, sort)
      end
    in
      S2.def sign
        {parameters = parameters',
         arguments = arguments,
         sort = sort,
         definiens = definiens'}
    end

  (* This extends bindDecl to work on signatures and maintains the
   * [opidTable] mapping string names their new symbol equivalents
   *)
  fun transport sign =
    let
      open StringTelescope.ConsView

      fun go opidTable (signIn : AstSignature.sign) (signOut : AbtSignature.sign) =
        case out signIn of
            Empty => signOut
          | Cons (opid, decl, rest) =>
            let
              val lbl = Symbol.named opid
              val decl' = bindDecl opidTable signOut decl
              val opidTable' = (opid, lbl) :: opidTable
              val signOut' = SymbolTelescope.snoc signOut (lbl, decl')
            in
              go opidTable' rest signOut'
            end
    in
      go [] sign SymbolTelescope.empty
    end
end
