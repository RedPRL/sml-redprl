functor Refiner (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  infixr @@
  infix 1 |> >> >: $$

  structure Rewrite =
  struct
    fun EvalGoal sign _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
        val (goal, _) = makeGoal @@ H >> CJ.CEQUIV (Machine.eval sign m, Machine.eval sign n)
        val psi = T.empty >: goal
      in
        (psi, fn rho => T.lookup rho @@ #1 goal)
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]
  end

  structure CEquiv =
  struct
    fun Refl _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
      in
        if Abt.eq (m, n) then
          (T.empty, fn _ => Abt.abtToAbs @@ Syn.into Syn.AX)
        else
          raise E.error [E.% "Expected", E.! m, E.% "to be alpha-equivalent to", E.! n]
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]
  end
end

