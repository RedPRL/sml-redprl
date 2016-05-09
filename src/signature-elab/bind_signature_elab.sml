(* This pass takes a signature of AST terms and assigns identity to their
 * symbols and variables. *)
structure BindSignatureElab : SIGNATURE_ELAB =
struct
  structure S1 = AstSignature
  structure S2 = AbtSignature

  open AstSignatureDecl

  structure MetaCtx =
  struct
    open Abt.Metavariable.Ctx
    structure Util = ContextUtil (structure Ctx = Abt.Metavariable.Ctx and Elem = Valence)
    open Util
  end

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
        val upsilon = List.foldl (fn ((u,tau),m) => NameEnv.insert m u tau) opidTable (ListPair.zipEq (localNames, localSymbols))
        val gamma = NameEnv.empty
        val mctx = List.foldl (fn (x, m) => MetaCtx.extend m x) MetaCtx.empty arguments
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
    | bindDecl opidTable sign (SYM_DECL sort) =
      S2.symDecl sign sort

  (* This extends bindDecl to work on signatures and maintains the
   * [opidTable] mapping string names their new symbol equivalents
   *)
  fun transport sign =
    let
      open AstToAbt StringTelescope.ConsView

      fun go opidTable (signIn : AstSignature.sign) (signOut : AbtSignature.sign) =
        case out signIn of
            EMPTY => signOut
          | CONS (opid, decl, rest) =>
            let
              val lbl = Symbol.named opid
              val decl' = bindDecl opidTable signOut decl
              val opidTable' = NameEnv.insert opidTable opid lbl
              val signOut' = SymbolTelescope.snoc signOut lbl decl'
            in
              go opidTable' rest signOut'
            end
    in
      go NameEnv.empty sign SymbolTelescope.empty
    end
end
