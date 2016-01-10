functor TransportSignature (Phi : SIGNATURE_MORPHISM) :
sig
  (* This lifts the [Phi.decl] operation which translates
   * just declarations into a full transformations on signatures
   * in the obvious recursive way.
   *)
  val transport : Phi.S1.sign -> Phi.S2.sign
end =
struct
  structure T1 =
  struct
    open Phi.S1.Telescope.SnocView
    open Phi.S1.Telescope
  end

  structure T2 = Phi.S2.Telescope

  fun *** (f, g) (x, y) =
    (f x, g y)

  infix ***

  fun transport sign =
    case T1.out sign of
         T1.Empty =>
           T2.empty
       | T1.Snoc (sign, l, decl) =>
           let
             val sign' = transport sign
             val decl' = Phi.decl sign' decl
             val l' = Phi.opid sign' l
           in
             T2.snoc sign' (l', decl')
           end
end
