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

  local
    open Lcf infix |>
  in
    fun subst (q, x) p =
      let
        val (psi |> evd, mainJdg) = p
        val (qpsi |> qevd, qjdg) = q

        val jdgx = Tl.lookup psi x
        val _ = if J.eq (qjdg, jdgx) then () else raise JudgmentMismatch (qjdg, jdgx)

        val rho = Env.singleton x qevd
        val psi' = Tl.splice qpsi x (Tl.modifyAfter x (J.subst rho) psi)
        val evd' = L.subst rho evd
      in
        (psi' |> evd', mainJdg)
      end
  end
end