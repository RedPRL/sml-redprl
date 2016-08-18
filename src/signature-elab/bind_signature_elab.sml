(* This pass takes a signature of AST terms and assigns identity to their
 * symbols and variables. *)
structure BindSignatureElab : SIGNATURE_ELAB =
struct
  structure S1 = AstSignature
  structure S2 = AbtSignature

  open AstSignatureDecl

  structure MetaCtx =
  struct
    open RedPrlAbt.Metavar.Ctx
    structure Util = ContextUtil (structure Ctx = RedPrlAbt.Metavar.Ctx and Elem = RedPrlAbt.O.Ar.Vl)
    open Util
  end

  fun liftValence ((ssorts, vsorts), tau) =
    ((List.map RedPrlOperator.S.EXP ssorts, List.map RedPrlOperator.S.EXP vsorts), RedPrlOperator.S.EXP tau)

  (* Given a AST declaration, this resolves its binding structure
   * in the context of the signature before it (given by [opidTable]).
   *)
  fun bindDecl opidTable sign (DEF {parameters, arguments, sort, definiens}, pos : Pos.t option) =
     (let
        val (localNames, sorts) = ListPair.unzip parameters
        val localSymbols = List.map Symbol.named localNames
        val parameters' = ListPair.zipEq (localSymbols, sorts)

        local
          open RedPrlAstToAbt
          val upsilon = List.foldl (fn ((u,tau),m) => NameEnv.insert m u tau) opidTable (ListPair.zipEq (localNames, localSymbols))
          val gamma = NameEnv.empty
          val mctx = List.foldl (fn ((x, vl), m) => MetaCtx.extend m (x, liftValence vl)) MetaCtx.empty arguments
        in
          val definiens' = convertOpen mctx (upsilon, gamma) (definiens, RedPrlOperator.S.EXP sort)
        end
      in
        S2.def sign
          ({parameters = parameters',
            arguments = arguments,
            sort = sort,
            definiens = definiens'}, pos)
      end handle exn => raise RedPrlExn.wrap pos exn)
    | bindDecl opidTable sign (SYM_DECL sort, pos) =
      S2.symDecl sign (sort, pos)

  (* This extends bindDecl to work on signatures and maintains the
   * [opidTable] mapping string names their new symbol equivalents
   *)
  fun transport sign =
    let
      open RedPrlAstToAbt StringTelescope.ConsView

      fun go opidTable (signIn : AstSignature.sign) (signOut : AbtSignature.sign) =
        case out signIn of
            EMPTY => signOut
          | CONS (opid, (decl, pos), rest) =>
            let
              val lbl = Symbol.named opid
              val decl' = bindDecl opidTable signOut (decl, pos)
              val opidTable' = NameEnv.insert opidTable opid lbl
              val signOut' = SymbolTelescope.snoc signOut lbl (decl', pos)
            in
              go opidTable' rest signOut'
            end
    in
      go NameEnv.empty sign SymbolTelescope.empty
    end
end
