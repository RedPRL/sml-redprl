structure Kernel :> KERNEL = 
struct
  structure Tm = RedPrlAbt
  structure Env = Tm.Metavar.Ctx

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

  exception JudgmentMismatch of jdg * jdg

  fun subst (q, x) p =
    let
      val (Lcf.|> (psi, evd), mainJdg) = p
      val (Lcf.|> (qpsi, qevd), qjdg) = q

      val jdgx = Lcf.Tl.lookup psi x
      val _ = if Lcf.J.eq (qjdg, jdgx) then () else raise JudgmentMismatch (qjdg, jdgx)

      val rho = Env.singleton x qevd
      val psi' = Lcf.Tl.splice qpsi x (Lcf.Tl.modifyAfter x (Lcf.J.subst rho) psi)
      val evd' = Lcf.L.subst rho evd
    in
      (Lcf.|> (psi', evd'), mainJdg)
    end
end