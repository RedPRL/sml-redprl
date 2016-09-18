functor Refiner (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  infixr @@
  infix 1 |>
  infix 2 >> >: $$ // \

  structure CEquiv =
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

    fun Refl _ jdg =
      let
        val H >> CJ.CEQUIV (m, n) = jdg
        val _ = assertAlphaEq (m, n)
      in
        (T.empty, fn _ => Abt.abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]
  end

  structure S1 =
  struct
    fun Type _ jdg =
      let
        val H >> CJ.TYPE a = jdg
        val Syn.S1 = Syn.out a
      in
        (T.empty, fn rho =>
          Abt.abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]

    fun EqBase _ jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S1 = Syn.out ty
        val Syn.BASE = Syn.out m
        val Syn.BASE = Syn.out n
      in
        (T.empty, fn rho => abtToAbs @@ Syn.into Syn.AX)
      end

    fun EqLoop _ jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S1 = Syn.out ty
        val Syn.LOOP r1 = Syn.out m
        val Syn.LOOP r2 = Syn.out n
      in
        if P.eq Sym.eq (r1, r2) then
          (T.empty, fn rho => abtToAbs @@ Syn.into Syn.AX)
        else
          raise E.error [E.% "Expected loops in same dimension"]
      end
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

    fun EqTT _ jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Syn.BOOL = Syn.out ty
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        (T.empty, fn rho => abtToAbs @@ Syn.into Syn.AX)
      end

    fun EqFF _ jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Syn.BOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        (T.empty, fn rho => abtToAbs @@ Syn.into Syn.AX)
      end

    fun Elim z _ jdg =
      let
        val H >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z

        val tt = Syn.into Syn.TT
        val ff = Syn.into Syn.FF

        val (goalT, _) = makeGoal @@ Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H >> CJ.TRUE (substVar (tt, z) cz)
        val (goalF, _) = makeGoal @@ Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H >> CJ.TRUE (substVar (ff, z) cz)

        val psi = T.empty >: goalT >: goalF
      in
        (psi, fn rho =>
           let
             val m = Syn.into @@ Syn.VAR (z, O.EXP)
             val t = T.lookup rho (#1 goalT) // ([],[])
             val f = T.lookup rho (#1 goalF) // ([],[])
           in
             abtToAbs o Syn.into @@ Syn.IF ((z, cz), m, (t, f))
           end)
      end
      handle Bind =>
        raise E.error [E.% "Expected bool elimination problem"]
  end

  structure DFun =
  struct
    fun Type alpha jdg =
      let
        val H >> CJ.TYPE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val bz = substVar (Syn.into @@ Syn.VAR (z, O.EXP), x) bx

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
        val bz = substVar (Syn.into @@ Syn.VAR (z, O.EXP), x) bx

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

  structure Path =
  struct
    fun Type alpha jdg =
      let
        val H >> CJ.TYPE ty = jdg
        val Syn.ID_TY ((u, a), m, n) = Syn.out ty

        val a0 = substSymbol (P.APP P.DIM0, u) a
        val a1 = substSymbol (P.APP P.DIM1, u) a

        val (tyGoal, _) = makeGoal @@ H >> CJ.TYPE a
        val (goal0, _) = makeGoal @@ H >> CJ.MEM (m, a0)
        val (goal1, _) = makeGoal @@ H >> CJ.MEM (n, a1)

        val psi = T.empty >: tyGoal >: goal0 >: goal1
      in
        (psi, fn rho =>
          abtToAbs @@ Syn.into Syn.AX)
      end

    fun True alpha jdg =
      let
        val H >> CJ.TRUE ty = jdg
        val Syn.ID_TY ((u, a), p0, p1) = Syn.out ty
        val a0 = substSymbol (P.APP P.DIM0, u) a
        val a1 = substSymbol (P.APP P.DIM1, u) a

        val v = alpha 0

        val (mainGoal, mhole) = makeGoal @@ ([(v, P.DIM)],[]) |> H >> CJ.TRUE (substSymbol (P.ret v, u) a)

        val m0 = mhole [(P.APP P.DIM0, P.DIM)] []
        val m1 = mhole [(P.APP P.DIM1, P.DIM)] []
        val (cohGoal0, _) = makeGoal @@ H >> CJ.EQ ((m0, p0), a0)
        val (cohGoal1, _) = makeGoal @@ H >> CJ.EQ ((m1, p1), a1)

        val psi = T.empty >: mainGoal >: cohGoal0 >: cohGoal1
      in
        (psi, fn rho =>
           let
             val ([v],_) \ p = outb @@ T.lookup rho (#1 mainGoal)
           in
             abtToAbs o Syn.into @@ Syn.ID_ABS (v, p)
           end)
      end
  end

  structure Generic =
  struct
    fun Intro alpha jdg =
      let
        val (U, G) |> jdg' = jdg
        val (goal, _) = makeGoal jdg'
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
      handle Bind =>
        raise E.error [E.% "Expected generic judgment"]
  end

  structure Hyp =
  struct
    fun Project z alpha jdg =
      let
        val H >> catjdg = jdg
        val catjdg' = lookupHyp H z
      in
        if CJ.eq (catjdg, catjdg') then
          (T.empty, fn rho =>
            abtToAbs o Syn.into @@ Syn.VAR (z, CJ.synthesis catjdg))
        else
          raise E.error [E.% "Hypothesis does not match goal"]
      end
      handle Bind =>
        raise E.error [E.% "Expected sequent judgment"]
  end

  structure Truth =
  struct
    fun Witness tm alpha jdg =
      let
        val H >> CJ.TRUE ty = jdg
        val (goal, _) = makeGoal @@ H >> CJ.MEM (tm, ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
          abtToAbs tm)
      end
      handle Bind =>
        raise E.error [E.% "Expected truth sequent"]
  end

  structure Membership =
  struct
    fun Intro alpha jdg =
      let
        val H >> CJ.MEM (tm, ty) = jdg
        val (goal, _) = makeGoal @@ H >> CJ.EQ ((tm, tm), ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
          abtToAbs @@ Syn.into Syn.AX)
      end
      handle Bind =>
        raise E.error [E.% "Expected member sequent"]
  end

  structure Equality =
  struct
    fun Hyp alpha jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = assertVarEq (x, y)
        val catjdg = lookupHyp H x
        val ty' =
          case catjdg of
             CJ.TRUE ty => ty
           | _ => raise E.error [E.% "Equality.Hyp: expected truth hypothesis"]
      in
        if Syn.Tm.eq (ty, ty') then
          (T.empty, fn rho => abtToAbs @@ Syn.into Syn.AX)
        else
          raise E.error [E.% @@ "Expected type of hypothesis " ^ Var.toString x ^ " to be", E.! ty, E.% "but found", E.! ty']
      end
      handle Bind =>
        raise E.error [E.% "Expected variable-equality sequent"]

    fun Symmetry alpha jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val (goal, _) = makeGoal @@ H >> CJ.EQ ((n, m), ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
           T.lookup rho (#1 goal))
      end

    fun HeadExpansion sign alpha jdg =
      let
        val H >> CJ.EQ ((m, n), ty) = jdg
        val Abt.$ (theta, _) = Abt.out m
        val hasFreeDims = List.exists (fn (_, sigma) => sigma = P.DIM) @@ Abt.O.support theta
        val _ = if hasFreeDims then raise E.error [E.% "Found free dimensions in head operator of", E.! m] else ()
        val m' = Machine.eval sign m
        val (goal, _) = makeGoal @@ H >> CJ.EQ ((m', n), ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
           T.lookup rho (#1 goal))
      end
  end

  local
    fun matchGoal f alpha jdg =
      f jdg alpha jdg
  in
    local
      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.DFUN _ => DFun.True
         | Syn.ID_TY _ => Path.True
         | _ => raise E.error [E.% "Could not find introduction rule for", E.! ty]

      fun StepType sign ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Type
         | Syn.DFUN _ => DFun.Type
         | Syn.ID_TY _ => Path.Type
         | Syn.S1 => S1.Type
         | _ => raise E.error [E.% "Could not find typehood rule for", E.! ty]

      fun StepEq sign ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.VAR _, Syn.VAR _, _) => Equality.Hyp
         | (Syn.TT, Syn.TT, Syn.BOOL) => Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Bool.EqFF
         | (Syn.BASE, Syn.BASE, Syn.S1) => S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => S1.EqLoop
         | (Syn.LOOP _, Syn.BASE, Syn.S1) => Equality.HeadExpansion sign
         | (Syn.BASE, Syn.LOOP _, Syn.S1) => Equality.Symmetry
         | _ => raise E.error [E.% "Could not find suitable equality rule for", E.! m, E.% "and", E.! n, E.% "at type", E.! ty]

      fun StepJdg sign = matchGoal
        (fn _ |> _ => Generic.Intro
          | _ >> CJ.TRUE ty => StepTrue sign ty
          | _ >> CJ.TYPE ty => StepType sign ty
          | _ >> CJ.MEM _ => Membership.Intro
          | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
          | jdg => raise E.error [E.% ("Could not find suitable rule for " ^ Seq.toString CJ.toString jdg)])
    in
      val Auto = StepJdg
    end

    local
      fun StepTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | _ => raise E.error [E.% "Could not find suitable elimination rule for", E.! ty]

      fun StepJdg sign z alpha jdg =
        let
          val H >> _ = jdg
          val catjdg = lookupHyp H z
        in
          case catjdg of
             CJ.TRUE ty => StepTrue ty z alpha jdg
           | _ => raise E.error [E.% ("Could not find suitable elimination rule for " ^ CJ.toString catjdg)]
        end
    in
      val Elim = StepJdg
    end
  end
end
