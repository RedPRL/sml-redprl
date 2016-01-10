(* This pass takes a signature of AST terms and assigns identity to their
 * symbols and variables. *)
structure BindSignatureMorphism : SIGNATURE_MORPHISM =
struct
  structure S1 = AstSignature
  structure S2 = AbtSignature

  open AstSignatureDecl

  fun metacontext xs =
    case xs of
         [] => Metacontext.empty
       | d :: xs => Metacontext.extend (metacontext xs) d

  fun decl sign (DEF {parameters, arguments, sort, definiens}) =
    let
      val (symbols, sorts) = ListPair.unzip parameters
      val symbols' = List.map Symbol.named symbols
      val parameters' = ListPair.zipEq (symbols', sorts)

      local
        open AstToAbt
        val upsilon = NameEnv.fromList (ListPair.zipEq (symbols, symbols'))
        val gamma = NameEnv.fromList []
        val mctx = metacontext arguments
      in
        val definiens' = convertOpen mctx (upsilon, gamma) (definiens, sort)
      end
    in
      S2.def
        {parameters = parameters',
         arguments = arguments,
         sort = sort,
         definiens = definiens'}
    end
end
