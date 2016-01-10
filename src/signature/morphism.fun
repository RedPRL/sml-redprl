functor TransportSignature (Phi : SIGNATURE_MORPHISM) :
sig
  (* This lifts the [Phi.decl] operation which translates
   * just declarations into a full transformations on signatures
   * in the obvious recursive way.
   *)
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

  fun transport sign =
    case T.out sign of
         T.Empty =>
           T.empty
       | T.Snoc (sign, l, decl) =>
           let
             val sign' = transport sign
             val decl' = Phi.decl sign' decl
           in
             T.snoc sign' (l, decl')
           end
end
