functor Refiner (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  infixr @@
  infix 1 |>
  infix 2 >> >: $$ // \

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

  structure Bool =
  struct
    fun Type _ jdg =
      let
        val H >> CJ.TYPE a = jdg
        val Syn.BOOL = Syn.out a
      in
        (T.empty, fn rho =>
          Abt.abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]
  end

  structure DFun =
  struct
    fun Type alpha jdg =
      let
        val H >> CJ.TYPE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val bz = substVar (check (`z, O.EXP), x) bx

        val (goal1, _) = makeGoal @@ H >> CJ.TYPE a
        val (goal2, _) = makeGoal @@ Hyps.snoc H z (CJ.TRUE a) >> CJ.TYPE bz
        val psi = T.empty >: goal1 >: goal2
      in
        (psi, fn rho =>
          Abt.abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected dfun typehood sequent"]

    fun True alpha jdg =
      let
        val H >> CJ.TRUE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val bz = substVar (check (`z, O.EXP), x) bx

        val (tyGoal, _) = makeGoal @@ H >> CJ.TYPE a
        val (goal, _) = makeGoal @@ ([],[(z, O.EXP)]) |> Hyps.snoc H z (CJ.TRUE a) >> CJ.TRUE bz
        val psi = T.empty >: goal >: tyGoal
      in
        (psi, fn rho =>
           let
             val (_, [x]) \ mx = outb @@ T.lookup rho (#1 goal)
           in
             abtToAbs o Syn.into @@ Syn.LAM (x, mx)
           end)
      end
      handle Bind =>
        raise E.error [E.% "Expected dfun truth sequent"]
  end

  structure Generic =
  struct
    (* TODO: this doesn't work, but it should! *)
    fun Intro alpha jdg =
      let
        val (U, G) |> jdg' = jdg
        val (goal, _) = makeGoal jdg
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
           let
             val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb @@ T.lookup rho (#1 goal)
             val (us', sigmas') = ListPair.unzip U
             val (xs', taus') = ListPair.unzip G
           in
             checkb ((us' @ us, xs' @ xs) \ m, ((sigmas' @ sigmas, taus' @ taus), tau))
           end)
      end
      handle Bind => raise E.error [E.% "ASDF!"]
  end

  local
    open Tacticals infix ORELSE
  in
    fun Auto sign alpha =
      Bool.Type alpha
        ORELSE DFun.Type alpha
        ORELSE DFun.True alpha
        ORELSE Generic.Intro alpha
  end
end

