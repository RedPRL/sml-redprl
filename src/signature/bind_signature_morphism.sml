(* This pass takes a signature of AST terms and assigns identity to their
 * symbols and variables. *)
structure BindSignatureMorphism : SIGNATURE_MORPHISM =
struct
  structure S1 = AstSignature
  structure S2 = AbtSignature

  type metacontext = Metacontext.t

  fun metacontext sign xs =
    case xs of
         [] => Metacontext.empty
       | d :: xs => Metacontext.extend (metacontext sign xs) d

  val symbol = Abt.Symbol.named

  fun metavariable x = x
  fun sort _ tau = tau
  fun valence _ vl = vl
  fun notation n = n

  fun term _ (mctx, sctx : S2.symbols, tau) ast =
    let
      open AstToAbt
      val upsilon =
        NameEnv.fromList
          (List.map
            (fn (u,tau) => (Symbol.Show.toString u, u))
            sctx)
      val gamma = NameEnv.fromList []
    in
      convertOpen mctx (upsilon, gamma) (ast, tau)
    end
end
