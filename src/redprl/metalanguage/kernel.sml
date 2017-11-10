structure Kernel :> KERNEL = 
struct
  structure Tm = RedPrlAbt

  type jdg = Lcf.jdg
  type meta = Lcf.L.var
  type name = Tm.variable
  type proof = jdg Lcf.state * jdg

  type rule = string

  exception todo fun ?e = raise e

  structure Rules = Refiner (Signature)

  fun init jdg =
    (Lcf.ret Lcf.isjdg jdg, jdg)

  fun rule jdg (rname, xs) =
    let
      fun alpha i =
        List.nth (xs, i)
        handle Subscript =>
          Tm.Var.named ("_" ^ Int.toString i)
    in
      (Rules.lookupRule rname alpha jdg, jdg)
    end

  fun concl (_, jdg) = jdg

  datatype action = 
    subst of proof * meta

  fun apply (acts, prf) = 
    case acts of 
       [] => prf
     | _ => ?todo

(* 
  fun subst (q, x) p =
    let
      val (Lcf.|> (psi, evd), _) = p
    in
      ?todo
    end *)
end