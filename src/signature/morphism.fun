functor TransportSignature (Phi : SIGNATURE_MORPHISM) :
sig
  val transport : Phi.S1.sign -> Phi.S2.sign
end =
struct
  structure T =
  struct
    open StringTelescope.SnocView
    open StringTelescope
  end

  fun *** (f, g) (x, y) =
    (f x, g y)

  infix ***

  fun transportDef sign def =
    let
      val Phi.S1.DEF (ys, args, tau, m) = Phi.S1.view def
      val ys' = List.map (Phi.symbol *** Phi.sort sign) ys
      val args' = List.map (Phi.metavariable *** Phi.valence sign) args
      val tau' = Phi.sort sign tau
      val mctx = Phi.metacontext sign args'
      val m' = Phi.term sign (mctx, ys', tau') m
    in
      Phi.S2.def (Phi.S2.DEF (ys', args', tau', m'))
    end

  fun transportDecl sign {def, notation} =
    {def = transportDef sign def,
     notation = Option.map Phi.notation notation}

  fun transport sign =
    case T.out sign of
         T.Empty =>
           T.empty
       | T.Snoc (sign, l, decl) =>
           let
             val sign' = transport sign
             val decl' = transportDecl sign' decl
           in
             T.snoc sign' (l, decl')
           end
end
