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
        val x = Metavar.named "?"
        val jdg' = RedPrlSequent.map (CJ.map (Machine.eval sign)) jdg
        val psi = T.empty >: (x, jdg')
      in
        (psi, fn rho => T.lookup rho x)
      end
  end

  structure CEquiv =
  struct
    fun Refl _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
        val _ = Abt.eq (m, n)
      in
        if Abt.eq (m, n) then
          (T.empty, fn _ => Abt.abtToAbs @@ O.MONO O.AX $$ [])
        else
          raise E.error [E.% "Expected", E.! m, E.% "to be alpha-equivalent to", E.! n]
      end
  end
end

