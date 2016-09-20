functor Refiner (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  infixr @@
  infix 1 |>
  infix 2 >> >: $$ $# // \ @>

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
    fun EqType _ jdg =
      let
        val H >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.S1 = Syn.out a
        val Syn.S1 = Syn.out b
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

    fun Elim z alpha jdg =
      let
        val H >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.S1 = Syn.out ty

        val u = alpha 0
        val loop = Syn.into o Syn.LOOP @@ P.ret u
        val base = Syn.into Syn.BASE
        val Hbase = Hyps.modifyAfter z (CJ.map (substVar (base, z))) H
        val cbase = substVar (base, z) cz

        val (goalB, holeB) = makeGoal @@ Hbase >> CJ.TRUE cbase
        val (goalL, holeL) = makeGoal @@ ([(u, P.DIM)], []) |> Hyps.modifyAfter z (CJ.map (substVar (loop, z))) H >> CJ.TRUE (substVar (loop, z) cz)

        val b = holeB [][]
        val l0 = holeL [(P.APP P.DIM0, P.DIM)] []
        val l1 = holeL [(P.APP P.DIM1, P.DIM)] []

        val (goalCoh0, _) = makeGoal @@ Hbase >> CJ.EQ ((l0, b), cbase)
        val (goalCoh1, _) = makeGoal @@ Hbase >> CJ.EQ ((l1, b), cbase)

        val psi = T.empty >: goalB >: goalL >: goalCoh0 >: goalCoh1
      in
        (psi, fn rho =>
           let
             val m = Syn.into @@ Syn.VAR (z, O.EXP)
             val b = T.lookup rho (#1 goalB) // ([],[])
             val lu = T.lookup rho (#1 goalL) // ([u],[])
           in
             abtToAbs o Syn.into @@ Syn.S1_ELIM ((z, cz), m, (b, (u, lu)))
           end)
      end
      handle Bind =>
        raise E.error [E.% "Expected circle elimination problem"]

    fun ElimEq alpha jdg =
      let
        val H >> CJ.EQ ((elim0, elim1), c) = jdg
        val Syn.S1_ELIM ((x, c0x), m0, (b0, (u, l0u))) = Syn.out elim0
        val Syn.S1_ELIM ((y, c1y), m1, (b1, (v, l1v))) = Syn.out elim1

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val c0z = substVar (ztm, x) c0x
        val c1z = substVar (ztm, y) c1y
        val l1u = substSymbol (P.ret u, v) l1v

        val l00 = substSymbol (P.APP P.DIM0, u) l0u
        val l01 = substSymbol (P.APP P.DIM1, u) l0u

        val cbase = substVar (Syn.into Syn.BASE, x) c0x
        val cloop = substVar (Syn.into @@ Syn.LOOP (P.ret u), x) c0x

        val S1 = Syn.into Syn.S1

        val (goalCz, _) = makeGoal @@ ([], [(z, O.EXP)]) |> H @> (z, CJ.TRUE S1) >> CJ.EQ_TYPE (c0z, c1z)
        val (goalM, _) = makeGoal @@ H >> CJ.EQ ((m0, m1), S1)
        val (goalB, _) = makeGoal @@ H >> CJ.EQ ((b0, b1), cbase)
        val (goalL, _) = makeGoal @@ H >> CJ.EQ ((l0u, l1u), cloop)
        val (goalL00, _) = makeGoal @@ H >> CJ.EQ ((l00, b0), cbase)
        val (goalL01, _) = makeGoal @@ H >> CJ.EQ ((l01, b0), cbase)

        val psi = T.empty >: goalCz >: goalM >: goalB >: goalL >: goalL00 >: goalL01
      in
        (psi, fn rho =>
           abtToAbs @@ Syn.into Syn.AX)
      end
  end

  structure Bool =
  struct
    fun EqType _ jdg =
      let
        val H >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
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
        val Syn.BOOL = Syn.out ty

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
    fun EqType alpha jdg =
      let
        val H >> CJ.EQ_TYPE (dfun0, dfun1) = jdg
        val Syn.DFUN (a0, x, b0x) = Syn.out dfun0
        val Syn.DFUN (a1, y, b1y) = Syn.out dfun1

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val b0z = substVar (ztm, x) b0x
        val b1z = substVar (ztm, y) b1y

        val (goal1, _) = makeGoal @@ H >> CJ.EQ_TYPE (a0, a1)
        val (goal2, _) = makeGoal @@ H @> (z, CJ.TRUE a0) >> CJ.EQ_TYPE (b0z, b1z)
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
        val (goal, _) = makeGoal @@ ([],[(z, O.EXP)]) |> H @> (z, CJ.TRUE a) >> CJ.TRUE bz
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

    fun Elim z alpha (jdg : J.judgment) =
      let
        val H >> catjdg = jdg
        val CJ.TRUE dfun = Hyps.lookup H z
        val Syn.DFUN (a, x, bx) = Syn.out dfun
        val (goal1, hole1) = makeGoal @@ H >> CJ.TRUE a

        val u = alpha 0
        val v = alpha 1

        val b' = substVar (hole1 [] [], x) bx

        val utm = Syn.into @@ Syn.VAR (u, O.EXP)
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val aptm = Syn.into @@ Syn.AP (ztm, hole1 [] [])
        val H' = Hyps.empty @> (u, CJ.TRUE b') @> (v, CJ.EQ ((utm, aptm), b'))
        val H'' = Hyps.interposeAfter H z H'
        val (goal2, _) = makeGoal @@ ([], [(u, O.EXP), (v, O.TRIV)]) |> H'' >> catjdg

        val psi = T.empty >: goal1 >: goal2
      in
        (psi, fn rho =>
          let
            val m = T.lookup rho (#1 goal1) // ([],[])
            val aptm = Syn.into @@ Syn.AP (ztm, m)
            val ax = Syn.into Syn.AX
          in
            abtToAbs @@ T.lookup rho (#1 goal2) // ([], [aptm, ax])
          end)
      end
  end

  structure Path =
  struct
    fun EqType alpha jdg =
      let
        val H >> CJ.EQ_TYPE (ty0, ty1) = jdg
        val Syn.ID_TY ((u, a0u), m0, n0) = Syn.out ty0
        val Syn.ID_TY ((v, a1v), m1, n1) = Syn.out ty1

        val a1u = substSymbol (P.ret u, v) a1v

        val a00 = substSymbol (P.APP P.DIM0, u) a0u
        val a01 = substSymbol (P.APP P.DIM1, u) a0u

        val (tyGoal, _) = makeGoal @@ H >> CJ.EQ_TYPE (a0u, a1u)
        val (goal0, _) = makeGoal @@ H >> CJ.EQ ((m0, m1), a00)
        val (goal1, _) = makeGoal @@ H >> CJ.EQ ((n0, n1), a01)

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
    fun splitList (xs, n) =
      (List.take (xs, n), List.drop (xs, n))
      handle _=> raise Fail "splitlist"

    fun liftTelescope (U, G) psi =
      let
        val (us', sigmas') = ListPair.unzip U
        val (xs', taus') = ListPair.unzip G

        open T.ConsView
        fun go EMPTY env psi' = psi'
          | go (CONS (x, jdg, psi)) env psi' =
              let
                 val vl as ((psorts, vsorts), tau) = J.evidenceValence jdg
                 val us = List.map (fn _ => Sym.named "u") psorts
                 val xs = List.map (fn _ => Var.named "x") vsorts

                 val ps = ListPair.map (fn (u, sigma) => (P.ret u, sigma)) (us' @ us, sigmas' @ psorts)
                 val ms = ListPair.map (fn (x, tau) => check (`x, tau)) (xs' @ xs, taus' @ vsorts)

                 val m = check (x $# (ps, ms), tau)
                 val b = checkb ((us, xs) \ m, vl)

                 val jdg' = (U, G) |> J.substEvidenceEnv env jdg
                 val env' = Metavar.Ctx.insert env x b
              in
                go (out psi) env' (T.snoc psi' x jdg')
              end
      in
        go (out psi) Metavar.Ctx.empty T.empty
      end

    structure ST = ShowTelescope (T)

    fun Lift tac alpha jdg =
      let
        val (U, G) |> jdg' = jdg

        val st as (psi, vld) = tac alpha jdg'

        val psi' = liftTelescope (U, G) psi

        val (us', sigmas') = ListPair.unzip U
        val (xs', taus') = ListPair.unzip G

        fun lower abs =
          let
            val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb abs
            val (us1, us2) = splitList (us, List.length U)
            val (sigmas1, sigmas2) = splitList (sigmas, List.length U)
            val (xs1, xs2) = splitList (xs, List.length G)
            val (taus1, taus2) = splitList (taus, List.length G)

            val srho = ListPair.foldl (fn (u1, (u', _), r) => Sym.Ctx.insert r u1 (P.ret u')) Sym.Ctx.empty (us1, U) handle _ => raise Fail "srho"
            val xrho = ListPair.foldl (fn (x1, (x', taux), r) => Var.Ctx.insert r x1 (check (`x', taux))) Var.Ctx.empty (xs1, G) handle _ => raise Fail "xrho"
            val m' = substVarenv xrho (substSymenv srho m)
          in
            checkb ((us2, xs2) \ m', ((sigmas2, taus2), tau))
          end

        fun lift abs =
          let
            val ((us, xs) \ m, ((sigmas, taus), tau)) = inferb abs
          in
            checkb ((us' @ us, xs' @ xs) \ m, ((sigmas' @ sigmas, taus' @ taus), tau))
          end

        fun vld' (rho : abs telescope) =
          lift o vld @@ T.foldl (fn (x, _, r) => T.modify x lower r) rho psi

      in
        (psi', vld')
      end
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

  structure Type =
  struct
    fun Intro _ jdg =
      let
        val H >> CJ.TYPE ty = jdg
        val (goal, _) = makeGoal @@ H >> CJ.EQ_TYPE (ty, ty)
        val psi = T.empty >: goal
      in
        (psi, fn rho =>
           T.lookup rho (#1 goal))
      end
      handle Bind =>
        raise E.error [E.% @@ "Expected typehood sequent but got " ^ J.judgmentToString jdg]
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
        raise E.error [E.% @@ "Expected truth sequent but got " ^ J.judgmentToString jdg]
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

  fun Lift tac alpha jdg =
    case jdg of
       _ |> _ => Generic.Lift (Lift tac) alpha jdg
     | _ >> _ => tac alpha jdg

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

      fun StepEqType sign (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Bool.EqType
         | (Syn.DFUN _, Syn.DFUN _) => DFun.EqType
         | (Syn.ID_TY _, Syn.ID_TY _) => Path.EqType
         | (Syn.S1, Syn.S1) => S1.EqType
         | _ => raise E.error [E.% "Could not find type equality rule for", E.! ty1, E.% "and", E.! ty2]

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
        (fn _ >> CJ.TRUE ty => StepTrue sign ty
          | _ >> CJ.EQ_TYPE tys => StepEqType sign tys
          | _ >> CJ.TYPE ty => Type.Intro
          | _ >> CJ.MEM _ => Membership.Intro
          | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
          | jdg => raise E.error [E.% ("Could not find suitable rule for " ^ Seq.toString CJ.toString jdg)])
    in
      val AutoStep = StepJdg
    end

    local
      fun StepTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.S1 => S1.Elim
         | Syn.DFUN _ => DFun.Elim
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
