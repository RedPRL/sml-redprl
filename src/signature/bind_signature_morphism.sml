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

  fun opid sign l =
    Symbol.named l

  local
    open SymbolTelescope SymbolTelescope.SnocView
  in
    fun makeOpidTable sign =
      case out sign of
           Empty => []
         | Snoc (sign, l, _) => (Symbol.Show.toString l, l) :: makeOpidTable sign
  end

  fun decl sign (DEF {parameters, arguments, sort, definiens}) =
    let
      val opidTable = makeOpidTable sign
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
      S2.def
        {parameters = parameters',
         arguments = arguments,
         sort = sort,
         definiens = definiens'}
    end
end
