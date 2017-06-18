functor Refiner (Sig : MINI_SIGNATURE) : REFINER =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = abt CJ.jdg
  type opid = Sig.opid

  infixr @@
  infix 1 ||
  infix 2 >> >: $$ $# // \ @>

  val op|| = Lcf.||
  fun #> (psi, m) = Lcf.|> (psi, abtToAbs m)
  infix #>

  val trivial = Syn.into Syn.AX

  fun orelse_ (t1, t2) alpha = Lcf.orelse_ (t1 alpha, t2 alpha)

  structure CEquiv =
  struct
    fun EvalGoal sign _ jdg =
      let
        val _ = RedPrlLog.trace "CEquiv.EvalGoal"
        val (I, H) >> CJ.CEQUIV (m, n) = jdg
        val (goal, hole) = makeGoal @@ ([],[]) || (I, H) >> CJ.CEQUIV (Machine.eval sign m, Machine.eval sign n)
      in
        T.empty >: goal
          #> hole [] []
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]

    fun Refl _ jdg =
      let
        val _ = RedPrlLog.trace "CEquiv.Refl"
        val (I, H) >> CJ.CEQUIV (m, n) = jdg
        val _ = assertAlphaEq (m, n)
      in
        T.empty #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected a computational equality sequent"]
  end

  structure S1 =
  struct
    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqType"
        val (I, H) >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.S1 = Syn.out a
        val Syn.S1 = Syn.out b
      in
        T.empty #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]

    fun EqBase _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqBase"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S1 = Syn.out ty
        val Syn.BASE = Syn.out m
        val Syn.BASE = Syn.out n
      in
        T.empty #> trivial
      end

    fun EqLoop _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqLoop"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S1 = Syn.out ty
        val Syn.LOOP r1 = Syn.out m
        val Syn.LOOP r2 = Syn.out n
        val () = assertParamEq "S1.EqLoop" (r1, r2)
      in
        T.empty #> trivial
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.S1 = Syn.out ty

        val u = alpha 0
        val loop = Syn.into o Syn.LOOP @@ P.ret u
        val base = Syn.into Syn.BASE
        val Hbase = Hyps.modifyAfter z (CJ.map (substVar (base, z))) H
        val cbase = substVar (base, z) cz

        val (goalB, holeB) = makeGoal @@ ([],[]) || (I, Hbase) >> CJ.TRUE cbase
        val (goalL, holeL) = makeGoal @@ ([(u, P.DIM)], []) || (I @ [(u, P.DIM)], Hyps.modifyAfter z (CJ.map (substVar (loop, z))) H) >> CJ.TRUE (substVar (loop, z) cz)

        val b = holeB [][]
        val l0 = holeL [(P.APP P.DIM0, P.DIM)] []
        val l1 = holeL [(P.APP P.DIM1, P.DIM)] []

        val (goalCoh0, _) = makeGoal @@ ([],[]) || (I, Hbase) >> CJ.EQ ((l0, b), cbase)
        val (goalCoh1, _) = makeGoal @@ ([],[]) || (I, Hbase) >> CJ.EQ ((l1, b), cbase)

        val psi = T.empty >: goalB >: goalL >: goalCoh0 >: goalCoh1

        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val elim = Syn.into @@ Syn.S1_ELIM ((z, cz), ztm, (holeB [] [], (u, holeL [(P.ret u, P.DIM)] [])))
      in
        psi #> elim
      end
      handle Bind =>
        raise E.error [E.% "Expected circle elimination problem"]

    fun ElimEq alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.ElimEq"
        val (I, H) >> CJ.EQ ((elim0, elim1), c) = jdg
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

        val (goalCz, _) = makeGoal @@ ([], [(z, O.EXP)]) || (I, H @> (z, CJ.TRUE S1)) >> CJ.EQ_TYPE (c0z, c1z)
        val (goalM, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), S1)
        val (goalB, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((b0, b1), cbase)
        val (goalL, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((l0u, l1u), cloop)
        val (goalL00, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((l00, b0), cbase)
        val (goalL01, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((l01, b0), cbase)

        val psi = T.empty >: goalCz >: goalM >: goalB >: goalL >: goalL00 >: goalL01
      in
        psi #> trivial
      end
  end

  structure Bool =
  struct
    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqType"
        val (I, H) >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
      in
        T.empty #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqTT"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.BOOL = Syn.out ty
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> trivial
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.BOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> trivial
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.BOOL = Syn.out ty

        val tt = Syn.into Syn.TT
        val ff = Syn.into Syn.FF

        val (goalT, holeT) = makeGoal @@ ([],[]) || (I, Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H) >> CJ.TRUE (substVar (tt, z) cz)
        val (goalF, holeF) = makeGoal @@ ([],[]) || (I, Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H) >> CJ.TRUE (substVar (ff, z) cz)

        val psi = T.empty >: goalT >: goalF
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val if_ = Syn.into @@ Syn.IF ((z, cz), ztm, (holeT [] [], holeF [] []))
      in
        psi #> if_
      end
      handle Bind =>
        raise E.error [E.% "Expected bool elimination problem"]

    fun ElimEq alpha jdg =
      let
        val _ = RedPrlLog.trace "Bool.ElimEq"
        val (I, H) >> CJ.EQ ((if0, if1), c) = jdg
        val Syn.IF ((x, c0x), m0, (t0, f0)) = Syn.out if0
        val Syn.IF ((y, c1y), m1, (t1, f1)) = Syn.out if1

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val c0z = substVar (ztm, x) c0x
        val c1z = substVar (ztm, y) c1y
        val c0tt = substVar (Syn.into Syn.TT, x) c0x
        val c0ff = substVar (Syn.into Syn.FF, x) c0x
        val c0m0 = substVar (m0, x) c0x

        val (goalTy, _) = makeGoal @@ ([], [(z, O.EXP)]) || (I, H @> (z, CJ.TRUE @@ Syn.into Syn.BOOL)) >> CJ.EQ_TYPE (c0z, c1z)
        val (goalTy', _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (c0m0, c)
        val (goalM, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), Syn.into Syn.BOOL)
        val (goalT, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((t0, t1), c0tt)
        val (goalF, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((f0, f1), c0ff)
        val psi = T.empty >: goalTy >: goalM >: goalT >: goalF
      in
        psi #> trivial
      end
  end

  structure StrictBool =
  struct
    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.EqType"
        val (I, H) >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.S_BOOL = Syn.out a
        val Syn.S_BOOL = Syn.out b
      in
        T.empty #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.EqTT"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S_BOOL = Syn.out ty
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> trivial
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S_BOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> trivial
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.S_BOOL = Syn.out ty

        val tt = Syn.into Syn.TT
        val ff = Syn.into Syn.FF

        val (goalT, holeT) = makeGoal @@ ([],[]) || (I, Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H) >> CJ.TRUE (substVar (tt, z) cz)
        val (goalF, holeF) = makeGoal @@ ([],[]) || (I, Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H) >> CJ.TRUE (substVar (ff, z) cz)

        val psi = T.empty >: goalT >: goalF
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val if_ = Syn.into @@ Syn.S_IF (ztm, (holeT [] [], holeF [] []))
      in
        psi #> if_
      end
      handle Bind =>
        raise E.error [E.% "Expected strict bool elimination problem"]

    fun ElimEq alpha jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.ElimEq"
        val (I, H) >> CJ.EQ ((if0, if1), c) = jdg
        val Syn.S_IF (m0, (t0, f0)) = Syn.out if0
        val Syn.S_IF (m1, (t1, f1)) = Syn.out if1

        val (goalM, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), Syn.into Syn.S_BOOL)
        val (goalT, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((t0, t1), c)
        val (goalF, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((f0, f1), c)
        val psi = T.empty >: goalM >: goalT >: goalF
      in
        psi #> trivial
      end

    fun EqElim z _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.EqElim"
        val (I, H) >> catjdg = jdg
        val CJ.EQ ((m0z, m1z), cz) = catjdg

        val CJ.TRUE ty = lookupHyp H z
        val Syn.S_BOOL = Syn.out ty

        val tt = Syn.into Syn.TT
        val ff = Syn.into Syn.FF

        val (goalM0, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (m0z, cz)
        val (goalM1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (m1z, cz)
        val (goalT, _) = makeGoal @@ ([],[]) || (I, Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H) >> CJ.map (substVar (tt, z)) catjdg
        val (goalF, _) = makeGoal @@ ([],[]) || (I, Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H) >> CJ.map (substVar (ff, z)) catjdg

        val psi = T.empty >: goalM0 >: goalM1 >: goalT >: goalF
      in
        psi #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected strict bool elimination problem"]
  end

  structure DProd =
  struct
    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.EqType"
        val (I, H) >> CJ.EQ_TYPE (dprod0, dprod1) = jdg
        val Syn.DPROD (a0, x, b0x) = Syn.out dprod0
        val Syn.DPROD (a1, y, b1y) = Syn.out dprod1

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val b0z = substVar (ztm, x) b0x
        val b1z = substVar (ztm, y) b1y

        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (a0, a1)
        val (goal2, _) = makeGoal @@ ([],[(x,O.EXP)]) || (I, H @> (z, CJ.TRUE a0)) >> CJ.EQ_TYPE (b0z, b1z)
      in
        T.empty >: goal1 >: goal2
          #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected dprod typehood sequent"]

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.Eq"
        val (I, H) >> CJ.EQ ((pair0, pair1), dprod) = jdg
        val Syn.PAIR (m0, n0) = Syn.out pair0
        val Syn.PAIR (m1, n1) = Syn.out pair1
        val Syn.DPROD (a, x, bx) = Syn.out dprod

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val bz = substVar (ztm, x) bx

        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), a)
        val (goal2, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((n0, n1), substVar (m0, x) bx)
        val (goalFam, _) = makeGoal @@ ([], [(z, O.EXP)]) || (I, H @> (z, CJ.TRUE a)) >> CJ.TYPE bz
      in
        T.empty >: goal1 >: goal2 >: goalFam
          #> trivial
      end

    fun Eta alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.Eta"
        val (I, H) >> CJ.EQ ((m, n), dprod) = jdg
        val Syn.DPROD (a, x, bx) = Syn.out dprod

        val m' = Syn.into @@ Syn.PAIR (Syn.into @@ Syn.FST m, Syn.into @@ Syn.SND m)
        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (m, dprod)
        val (goal2, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m', n), dprod)
      in
        T.empty >: goal1 >: goal2
          #> trivial
      end

    fun FstEq alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.FstEq"
        val (I, H) >> CJ.EQ ((fst0, fst1), ty) = jdg
        val Syn.FST m0 = Syn.out fst0
        val Syn.FST m1 = Syn.out fst1

        val (goalTy, holeTy) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m0
        val (goalTyA, holeTyA) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DPROD, 0, holeTy [] [], [], [])
        val (goalEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), holeTy [] [])
        val (goalEqTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (holeTyA [] [], ty)
      in
        T.empty >: goalTy >: goalTyA >: goalEq >: goalEqTy
          #> trivial
      end

    fun SndEq alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.SndEq"
        val (I, H) >> CJ.EQ ((snd0, snd1), ty) = jdg
        val Syn.SND m0 = Syn.out snd0
        val Syn.SND m1 = Syn.out snd1

        val (goalTy, holeTy) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m0
        val (goalTyB, holeTyB) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DPROD, 1, holeTy [] [], [], [Syn.into @@ Syn.FST m0])
        val (goalEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), holeTy [] [])
        val (goalEqTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (holeTyB [] [], ty)
      in
        T.empty >: goalTy >: goalTyB >: goalEq >: goalEqTy
          #> trivial
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.True"
        val (I, H) >> CJ.TRUE dprod = jdg
        val Syn.DPROD (a, x, bx) = Syn.out dprod

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val bz = substVar (ztm, x) bx

        val (goal1, hole1) = makeGoal @@ ([],[]) || (I, H) >> CJ.TRUE a
        val (goal2, hole2) = makeGoal @@ ([],[]) || (I, H) >> CJ.TRUE (substVar (hole1 [] [], x) bx)
        val (goalFam, _) = makeGoal @@ ([], [(z, O.EXP)]) || (I, H @> (z, CJ.TRUE a)) >> CJ.TYPE bz
        val psi = T.empty >: goal1 >: goal2 >: goalFam
        val pair = Syn.into @@ Syn.PAIR (hole1 [] [], hole2 [] [])
      in
        psi #> pair
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE dprod = Hyps.lookup H z
        val Syn.DPROD (a, x, bx) = Syn.out dprod

        val z1 = alpha 0
        val z2 = alpha 1

        val z1tm = Syn.into @@ Syn.VAR (z1, O.EXP)
        val z2tm = Syn.into @@ Syn.VAR (z2, O.EXP)

        val bz1 = substVar (z1tm, x) bx
        val pair = Syn.into @@ Syn.PAIR (z1tm, z2tm)

        val H' = Hyps.empty @> (z1, CJ.TRUE a) @> (z2, CJ.TRUE bz1)
        val H'' = Hyps.interposeAfter H z H'

        val (goal, hole) =
          makeGoal
            @@ ([], [(z1, O.EXP), (z2, O.EXP)])
            || (I, Hyps.modifyAfter z (CJ.map (substVar (pair, z))) H'')
            >> CJ.TRUE (substVar (pair, z) cz)

        val psi = T.empty >: goal

        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val fstz = Syn.into @@ Syn.FST ztm
        val sndz = Syn.into @@ Syn.SND ztm
      in
        T.empty >: goal
          #> hole [] [fstz, sndz]
      end
  end

  structure DFun =
  struct
    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.EqType"
        val (I, H) >> CJ.EQ_TYPE (dfun0, dfun1) = jdg
        val Syn.DFUN (a0, x, b0x) = Syn.out dfun0
        val Syn.DFUN (a1, y, b1y) = Syn.out dfun1

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val b0z = substVar (ztm, x) b0x
        val b1z = substVar (ztm, y) b1y

        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (a0, a1)
        val (goal2, _) = makeGoal @@ ([],[(z,O.EXP)]) || (I, H @> (z, CJ.TRUE a0)) >> CJ.EQ_TYPE (b0z, b1z)
      in
        T.empty >: goal1 >: goal2
          #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected dfun typehood sequent"]

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Eq"
        val (I, H) >> CJ.EQ ((lam0, lam1), dfun) = jdg
        val Syn.LAM (x, m0x) = Syn.out lam0
        val Syn.LAM (y, m1y) = Syn.out lam1
        val Syn.DFUN (a, z, bz) = Syn.out dfun

        val w = alpha 0
        val wtm = Syn.into @@ Syn.VAR (w, O.EXP)

        val m0w = substVar (wtm, x) m0x
        val m1w = substVar (wtm, y) m1y
        val bw = substVar (wtm, z) bz

        val (goal1, _) = makeGoal @@ ([],[(w, O.EXP)]) || (I, H @> (w, CJ.TRUE a)) >> CJ.EQ ((m0w, m1w), bw)
        val (goal2, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.TYPE a
      in
        T.empty >: goal1 >: goal2
          #> trivial
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.True"
        val (I, H) >> CJ.TRUE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val bz = substVar (ztm, x) bx

        val (tyGoal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.TYPE a
        val (goal, hole) = makeGoal @@ ([],[(z, O.EXP)]) || (I, H @> (z, CJ.TRUE a)) >> CJ.TRUE bz

        val psi = T.empty >: goal >: tyGoal
        val lam = Syn.into @@ Syn.LAM (z, hole [] [ztm])
      in
        psi #> lam
      end
      handle Bind =>
        raise E.error [E.% "Expected dfun truth sequent"]

    fun Eta alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Eta"
        val (I, H) >> CJ.EQ ((m, n), dfun) = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val xtm = Syn.into @@ Syn.VAR (x, O.EXP)
        val m' = Syn.into @@ Syn.LAM (x, Syn.into @@ Syn.AP (m, xtm))
        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (m, dfun)
        val (goal2, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m', n), dfun)
      in
        T.empty >: goal1 >: goal2
          #> trivial
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE dfun = Hyps.lookup H z
        val Syn.DFUN (a, x, bx) = Syn.out dfun
        val (goal1, hole1) = makeGoal @@ ([],[]) || (I, H) >> CJ.TRUE a

        val u = alpha 0
        val v = alpha 1

        val b' = substVar (hole1 [] [], x) bx

        val utm = Syn.into @@ Syn.VAR (u, O.EXP)
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val aptm = Syn.into @@ Syn.AP (ztm, hole1 [] [])
        val H' = Hyps.empty @> (u, CJ.TRUE b') @> (v, CJ.EQ ((utm, aptm), b'))
        val H'' = Hyps.interposeAfter H z H'

        val (goal2, hole2) = makeGoal @@ ([], [(u, O.EXP), (v, O.TRIV)]) || (I, H'') >> CJ.TRUE cz

        val psi = T.empty >: goal1 >: goal2
        val aptm = Syn.into @@ Syn.AP (ztm, hole1 [] [])
      in
        psi #> hole2 [] [aptm, Syn.into Syn.AX]
      end

    fun ApEq alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.ApEq"
        val (I, H) >> CJ.EQ ((ap0, ap1), c) = jdg
        val Syn.AP (m0, n0) = Syn.out ap0
        val Syn.AP (m1, n1) = Syn.out ap1

        val (goalDFun0, holeDFun0) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m0
        val (goalDFun1, holeDFun1) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m1
        val (goalDFunEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (holeDFun0 [] [], holeDFun1 [] [])
        val (goalDom, holeDom) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DFUN, 0, holeDFun0 [] [], [], [])
        val (goalM, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), holeDFun0 [] [])
        val (goalN, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((n0, n1), holeDom [] [])
      in
        T.empty >: goalDFun0 >: goalDFun1 >: goalDFunEq >: goalDom >: goalM >: goalN
          #> trivial
      end
  end

  structure Path =
  struct
    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.EqType"
        val (I, H) >> CJ.EQ_TYPE (ty0, ty1) = jdg
        val Syn.PATH_TY ((u, a0u), m0, n0) = Syn.out ty0
        val Syn.PATH_TY ((v, a1v), m1, n1) = Syn.out ty1

        val a1u = substSymbol (P.ret u, v) a1v

        val a00 = substSymbol (P.APP P.DIM0, u) a0u
        val a01 = substSymbol (P.APP P.DIM1, u) a0u

        val (tyGoal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (a0u, a1u)
        val (goal0, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), a00)
        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((n0, n1), a01)
      in
        T.empty >: tyGoal >: goal0 >: goal1
          #> trivial
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.True"
        val (I, H) >> CJ.TRUE ty = jdg
        val Syn.PATH_TY ((u, a), p0, p1) = Syn.out ty
        val a0 = substSymbol (P.APP P.DIM0, u) a
        val a1 = substSymbol (P.APP P.DIM1, u) a

        val v = alpha 0

        val (mainGoal, mhole) = makeGoal @@ ([(v, P.DIM)],[]) || (I, H) >> CJ.TRUE (substSymbol (P.ret v, u) a)

        val m0 = mhole [(P.APP P.DIM0, P.DIM)] []
        val m1 = mhole [(P.APP P.DIM1, P.DIM)] []
        val (cohGoal0, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, p0), a0)
        val (cohGoal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m1, p1), a1)

        val psi = T.empty >: mainGoal >: cohGoal0 >: cohGoal1
        val abstr = Syn.into @@ Syn.PATH_ABS (v, mhole [(P.ret v, P.DIM)] [])
      in
        psi #> abstr
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.Eq"
        val (I, H) >> CJ.EQ ((abs0, abs1), ty) = jdg
        val Syn.PATH_TY ((u, au), p0, p1) = Syn.out ty
        val Syn.PATH_ABS (v, m0v) = Syn.out abs0
        val Syn.PATH_ABS (w, m1w) = Syn.out abs1

        val z = alpha 0
        val az = substSymbol (P.ret z, u) au
        val m0z = substSymbol (P.ret z, v) m0v
        val m1z = substSymbol (P.ret z, w) m1w

        val a0 = substSymbol (P.APP P.DIM0, u) au
        val a1 = substSymbol (P.APP P.DIM1, u) au
        val m00 = substSymbol (P.APP P.DIM0, v) m0v
        val m01 = substSymbol (P.APP P.DIM1, v) m0v

        val (goalM, _) = makeGoal @@ ([(z, P.DIM)], []) || (I, H) >> CJ.EQ ((m0z, m1z), az)
        val (goalM00, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m00, p0), a0)
        val (goalM01, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m01, p1), a1)
      in
        T.empty >: goalM >: goalM00 >: goalM01
          #> trivial
      end

    fun ApEq alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.ApEq"
        val (I, H) >> CJ.EQ ((ap0, ap1), ty) = jdg
        val Syn.PATH_AP (m0, r0) = Syn.out ap0
        val Syn.PATH_AP (m1, r1) = Syn.out ap1
        val () = assertParamEq "Path.ApEq" (r0, r1)
        val (goalSynth, holeSynth) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m0
        val (goalMem, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), holeSynth [] [])
        val (goalLine, holeLine) = makeGoal @@ ([],[]) || MATCH (O.MONO O.PATH_TY, 0, holeSynth [] [], [r0], [])
        val (goalTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty, holeLine [] [])
      in
        T.empty >: goalSynth >: goalMem >: goalLine >: goalTy
          #> trivial
      end

    fun ApComputeConst alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.ApComputeConst"
        val (I, H) >> CJ.EQ ((ap, p), a) = jdg
        val Syn.PATH_AP (m, P.APP r) = Syn.out ap
        val (goalSynth, holeSynth) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m

        val dimAddr = case r of P.DIM0 => 1 | P.DIM1 => 2
        val (goalLine, holeLine) = makeGoal @@ ([],[]) || MATCH (O.MONO O.PATH_TY, 0, holeSynth [] [], [P.APP r], [])
        val (goalEndpoint, holeEndpoint) = makeGoal @@ ([],[]) || MATCH (O.MONO O.PATH_TY, dimAddr, holeSynth [] [], [], [])
        val (goalTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (a, holeLine [] [])
        val (goalEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((holeEndpoint [] [], p), a)
      in
        T.empty >: goalSynth >: goalLine >: goalEndpoint >: goalTy >: goalEq
          #> trivial
      end

    fun Eta alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.Eta"
        val (I, H) >> CJ.EQ ((m, n), pathTy) = jdg
        val Syn.PATH_TY ((u, a), p0, p1) = Syn.out pathTy

        val m' = Syn.into @@ Syn.PATH_ABS (u, Syn.into @@ Syn.PATH_AP (m, P.ret u))
        val (goal1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (m, pathTy)
        val (goal2, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m', n), pathTy)
      in
        T.empty >: goal1 >: goal2
          #> trivial
      end

  end

  structure Hyp =
  struct
    fun Project z alpha jdg =
      let
        val _ = RedPrlLog.trace "Hyp.Project"
        val (I, H) >> catjdg = jdg
        val catjdg' = lookupHyp H z
      in
        if CJ.eq (catjdg, catjdg') then
          T.empty #> Syn.into (Syn.VAR (z, CJ.synthesis catjdg))
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
        val _ = RedPrlLog.trace "Type.Intro"
        val (I, H) >> CJ.TYPE ty = jdg
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty, ty)
      in
        T.empty >: goal
          #> trivial
      end
      handle Bind =>
        raise E.error [E.% @@ "Expected typehood sequent but got " ^ J.toString jdg]

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Type.Elim"
        val (I, H) >> catjdg = jdg
        val CJ.TYPE ty = lookupHyp H z
        val H' = Hyps.modify z (fn _ => CJ.EQ_TYPE (ty, ty)) H
        val (goal, hole) = makeGoal @@ ([],[]) || (I, H') >> catjdg
      in
        T.empty >: goal
          #> hole [] []
      end
  end


  structure TypeEquality =
  struct
    fun Symmetry alpha jdg =
    let
      val _ = RedPrlLog.trace "Equality.Symmetry"
      val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
      val (goal, hole) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty2, ty1)
    in
      T.empty >: goal
        #> trivial
    end
  end

  structure Truth =
  struct
    fun Witness tm alpha jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> CJ.TRUE ty = jdg
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (tm, ty)
      in
        T.empty >: goal
          #> tm
      end
      handle Bind =>
        raise E.error [E.% @@ "Expected truth sequent but got " ^ J.toString jdg]
  end

  structure Membership =
  struct
    fun Intro alpha jdg =
      let
        val _ = RedPrlLog.trace "Membership.Intro"
        val (I, H) >> CJ.MEM (tm, ty) = jdg
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((tm, tm), ty)
      in
        T.empty >: goal
          #> trivial
      end
      handle Bind =>
        raise E.error [E.% "Expected member sequent"]
  end

  structure Synth =
  struct
    fun FromWfHyp z alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Switch"
        val (I, H) >> CJ.SYNTH tm = jdg
        val CJ.EQ ((a, b), ty) = Hyps.lookup H z
      in
        if Abt.eq (a, tm) orelse Abt.eq (b, tm) then
          T.empty #> ty
        else
          raise Fail "Did not match"
      end

    fun Hyp alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Hyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val CJ.TRUE a = Hyps.lookup H z
      in
        T.empty #> a
      end

    fun Ap alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Ap"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.AP (m, n) = Syn.out tm
        val (goalDFun, holeDFun) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m
        val (goalDom, holeDom) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DFUN, 0, holeDFun [] [], [], [])
        val (goalCod, holeCod) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DFUN, 1, holeDFun [] [], [], [n])
        val (goalN, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (n, holeDom [] [])
      in
        T.empty >: goalDFun >: goalDom >: goalCod >: goalN
          #> holeCod [] []
      end

    fun S1Elim alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.S1Elim"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.S1_ELIM ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (tm, cm)
      in
        T.empty >: goal
          #> cm
      end

    fun If alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.If"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.IF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (tm, cm)
      in
        T.empty >: goal
          #> cm
      end

    fun PathAp alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.PathAp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.PATH_AP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m
        val (goalLine, holeLine) = makeGoal @@ ([],[]) || MATCH (O.MONO O.PATH_TY, 0, holePathTy [] [], [r], [])
        val psi = T.empty >: goalPathTy >: goalLine
      in
        T.empty >: goalPathTy >: goalLine
          #> holeLine [] []
      end

    fun Fst alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Fst"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.FST m = Syn.out tm
        val (goalTy, holeTy) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m
        val (goalA, holeA) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DPROD, 0, holeTy [] [], [], [])
      in
        T.empty >: goalTy >: goalA
          #> holeA [] []
      end

    fun Snd alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Snd"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.SND m = Syn.out tm
        val (goalTy, holeTy) = makeGoal @@ ([],[]) || (I, H) >> CJ.SYNTH m
        val (goalB, holeB) = makeGoal @@ ([],[]) || MATCH (O.MONO O.DPROD, 1, holeTy [] [], [], [Syn.into @@ Syn.FST m])
      in
        T.empty >: goalTy >: goalB
          #> holeB [] []
      end
  end

  structure Match =
  struct
    fun MatchOperator alpha jdg =
      let
        val _ = RedPrlLog.trace "Match.MatchOperator"
        val MATCH (th, k, tm, ps, ms) = jdg

        val Abt.$ (th', args) = Abt.out tm
        val true = Abt.O.eq Sym.eq (th, th')

        val (vls, _) = Abt.O.arity th
        val (us, xs) \ arg = List.nth (args, k)
        val srho = ListPair.foldrEq (fn (u,p,rho) => Sym.Ctx.insert rho u p) Sym.Ctx.empty (us, ps)
        val vrho = ListPair.foldrEq (fn (x,m,rho) => Var.Ctx.insert rho x m) Var.Ctx.empty (xs, ms)

        val arg' = substSymenv srho (substVarenv vrho arg)
      in
        T.empty #> arg'
      end
      handle _ =>
        raise E.error [E.% "MATCH judgment failed to unify"]
  end

  structure Equality =
  struct
    fun Hyp alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.Hyp"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
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
          T.empty #> trivial
        else
          raise E.error [E.% @@ "Expected type of hypothesis " ^ Var.toString x ^ " to be", E.! ty, E.% "but found", E.! ty']
      end
      handle Bind =>
        raise E.error [E.% "Expected variable-equality sequent"]

    fun Symmetry alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val (goal, hole) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((n, m), ty)
      in
        T.empty >: goal
          #> trivial
      end
  end

  structure Restriction :
  sig
    (* This structure used to provide functions that automate the
       restriction judgement rules given in "Dependent Cubical
       Realizability", page 46.

       On 2017/06/14, favonia implemented a function to handle
       all cases. We need to generalize the old handling to
       welcome new hcom operators. (It is true that we still
       only need to handle context restrictions with at most two
       equations, but it seems easier to just handle all cases.)

       Such automation is possible because the rules are "syntax
       directed" on the restriction being performed.
     *)

    (* Restrict a judgement (as the goal) by a list of equations.
     * Returns NONE if the resulting judgement is vacuously true.
     *)
    val restrict : abt jdg -> (param * param) list -> abt jdg option
  end
  =
  struct
    (* A helper function which does substitution in a parameter. *)
    fun substSymInParam (r, v) = P.bind (fn u => if Sym.eq (u, v) then r else P.ret u)

    fun restrict jdg [] = SOME jdg
      | restrict jdg ((P.APP d1, P.APP d2) :: eqs) =
          (* The following line is correct because we only have constants
           * (DIM0 and DIM1). If in the future we want to have connections
           * or other stuff, then a real unification algorithm might be needed.
           *)
          if P.Sig.eq (fn _ => true) (d1, d2) then restrict jdg eqs else NONE
      | restrict jdg ((r1 as P.VAR v1, r2) :: eqs) =
          if P.eq Sym.eq (r1, r2) then restrict jdg eqs else substAndRestrict (r2, v1) jdg eqs
      | restrict jdg ((r1, r2 as P.VAR v2) :: eqs) =
          substAndRestrict (r1, v2) jdg eqs

    and substAndRestrict rv jdg eqs = restrict
          (Seq.map (substSymbol rv) jdg)
          (List.map (fn (r, r') => (substSymInParam rv r, substSymInParam rv r')) eqs)
  end

  (* code shared by Com, HCom and FHCom. *)
  structure ComKit =
  struct
    (* todo: optimizing the restriction process even further. *)
    (* todo: pre-restrict r=0, r=1, 0=r and 1=r, and open-reduce everything first. *)
    (* todo: do alpha-renaming only once. *)
    (* todo: try to minimize substitution. *)

    (* Produce the list of goals requiring that tube aspects agree with each other.
         forall i <= j.
           N_i = P_j in A [Psi, y | r_i = r_i', r_j = r_j']
     *)
    fun appendInterTubeGoals tele (I, H) w ty tubes0 tubes1 =
      let
        fun interTube (eq0, (u, tube0)) (eq1, (v, tube1)) =
          let
            val tube0 = substSymbol (P.ret w, u) tube0
            val tube1 = substSymbol (P.ret w, v) tube1
            val J = (I, H) >> CJ.EQ ((tube0, tube1), ty)
          in
            Option.map 
              (fn j => #1 (makeGoal (([(w, P.DIM)], []) || j)))
              (Restriction.restrict J [eq0, eq1])
          end
        fun goTubePairs [] [] = []
          | goTubePairs (t0 :: ts0) (t1 :: ts1) =
              List.mapPartial (interTube t0) (t1 :: ts1) :: goTubePairs ts0 ts1
          | goTubePairs _ _ = raise Fail "interTubeGoals: the tubes are of different lengths"
      in
        List.foldl (fn (l, t) => appendListOfGoals (t, l)) tele (goTubePairs tubes0 tubes1)
      end

    (* Produce the list of goals requiring that tube aspects agree with the cap.
         forall i.
           N_i<r/y> = M in A [Psi | r_i = r_i']
     *)
    fun appendTubeCapGoals tele (I, H) ty r cap tubes =
      let
        fun tubeCap (eq, (u, tube)) =
          let
            val J = (I, H) >> CJ.EQ ((substSymbol (r,u) tube, cap), ty)
          in
            Option.map (#1 o (fn j => makeGoal @@ ([],[]) || j)) (Restriction.restrict J [eq])
          end
      in
        appendListOfGoals (tele, List.mapPartial tubeCap tubes)
      end
  end

  structure HCom =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.HCOM {dir=(r0, r'0), ty=ty0, cap=cap0, tubes=tubes0} = Syn.out lhs
        val () = assertAlphaEq (ty0, ty)
        val Syn.HCOM {dir=(r1, r'1), ty=ty1, cap=cap1, tubes=tubes1} = Syn.out rhs
        val () = assertParamEq "HCom.Eq source of direction" (r0, r1)
        val () = assertParamEq "HCom.Eq target of direction" (r'0, r'1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = ListPair.mapEq (assertEquationEq "HCom.Eq equations") (eqs0, eqs1)
        val _ = assertTautologicalEquations "HCom.Eq tautology checking" eqs0

        val (goalTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty0, ty1)
        val (goalCap, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((cap0, cap1), ty)

        val w = alpha 0
      in
        ComKit.appendTubeCapGoals
          (ComKit.appendInterTubeGoals
            (T.empty >: goalTy >: goalCap)
            (I, H) w ty tubes0 tubes1)
          (I, H) ty r0 cap0 tubes0
        #> trivial
      end

    fun CapEq alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.CapEq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out lhs
        val () = assertParamEq "HCom.CapEq source and target of direction" (r, r')
        val () = assertAlphaEq (ty0, ty)

        val (goalTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.TYPE ty
        val (goalEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((cap, rhs), ty)

        val w = alpha 0
      in
        ComKit.appendTubeCapGoals
          (ComKit.appendInterTubeGoals
            (T.empty >: goalTy >: goalEq)
            (I, H) w ty tubes tubes)
          (I, H) ty r cap tubes
        #> trivial
      end

    (* Search for the first satisfied equation in an hcom. *)
    fun TubeEq alpha jdg =
      let
        val _ = RedPrlLog.trace "HCom.TubeEq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.HCOM {dir=(r, r'), ty=ty0, cap, tubes} = Syn.out lhs
        val (eq, (u, tube)) = Option.valOf (List.find (fn (eq, _) => P.eq Sym.eq eq) tubes)
        val () = assertAlphaEq (ty0, ty)

        val (goalTy, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.TYPE ty
        val (goalCap, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.MEM (cap, ty)
        val (goalEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((substSymbol (r', u) tube, rhs), ty)

        val w = alpha 0
      in
        ComKit.appendTubeCapGoals
          (ComKit.appendInterTubeGoals
            (T.empty >: goalTy >: goalCap >: goalEq)
            (I, H) w ty tubes tubes)
          (I, H) ty r cap tubes
        #> trivial
      end

    local
      infix orelse_
    in
      (* Try all the hcom rules. *)
      val AutoEq = Eq orelse_ CapEq orelse_ TubeEq
    end
  end

  structure FHCom =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "FHCom.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.FHCOM {dir=(r0, r'0), cap=cap0, tubes=tubes0} = Syn.out lhs
        val Syn.FHCOM {dir=(r1, r'1), cap=cap1, tubes=tubes1} = Syn.out rhs
        val () = assertParamEq "FHCom.Eq source of direction" (r0, r1)
        val () = assertParamEq "FHCom.Eq target of direction" (r'0, r'1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = ListPair.mapEq (assertEquationEq "FHCom.Eq equations") (eqs0, eqs1)
        val _ = assertTautologicalEquations "FHCom.Eq tautology checking" eqs0

        val (goalCap, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((cap0, cap1), ty)

        val w = alpha 0
      in
        ComKit.appendTubeCapGoals
          (ComKit.appendInterTubeGoals
            (T.empty >: goalCap)
            (I, H) w ty tubes0 tubes1)
          (I, H) ty r0 cap0 tubes0
        #> trivial
      end

    local
      infix orelse_
    in
      (* Try all the fhcom rules. *)
      val AutoEq = Eq
    end
  end

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COE {dir=(r0, r'0), ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=(r1, r'1), ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = assertParamEq "Coe.Eq source of direction" (r0, r1)
        val () = assertParamEq "Coe.Eq target of direction" (r'0, r'1)

        val ty01 = substSymbol (r'0, u) ty0u
        val (goalTy1, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty01, ty)

        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u) ty0u
        val ty1w = substSymbol (P.ret w, v) ty1v
        val (goalTy, _) = makeGoal @@ ([(w, P.DIM)],[]) || (I, H) >> CJ.EQ_TYPE (ty0w, ty1w)

        val ty00 = substSymbol (r0, u) ty0u
        val (goalCoercees, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m0, m1), ty00)
      in
        T.empty >: goalTy1 >: goalTy >: goalCoercees #> trivial
      end

    fun CapEq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.CapEq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COE {dir=(r, r'), ty=(u, tyu), coercee=m} = Syn.out lhs
        val () = assertParamEq "Coe.CapEq source and target of direction" (r, r')

        val ty0 = substSymbol (r, u) tyu
        val (goalTy0, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty0, ty)

        val (goalTy, _) = makeGoal @@ ([(u, P.DIM)],[]) || (I, H) >> CJ.TYPE tyu
        val (goalEq, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m, rhs), ty)
      in
        T.empty >: goalTy0 >: goalTy >: goalEq #> trivial
      end

    local
      infix orelse_
    in
      (* Try all the fhcom rules. *)
      val AutoEq = Eq orelse_ CapEq
    end
  end

  structure Computation =
  struct
    local
      open Machine.S.Cl infix <: $
    in
      (* This should be safe---but it is not ideal, because we have to force the deferred
       * substitutions in order to determine whether it is safe to take a step. *)
      fun safeStep sign (st as (mode, cl, stk)) : abt Machine.S.state option =
        let
          val m = force cl
        in
          case (out m, Machine.canonicity sign m) of
             (_, Machine.CANONICAL) => Machine.next sign st
           | (O.POLY (O.CUST _) $ _, _) => Machine.next sign st
           | (th $ _, _) =>
               if List.exists (fn (_, sigma) => sigma = P.DIM) @@ Abt.O.support th then
                 raise Fail ("Unsafe step: " ^ TermPrinter.toString m)
               else
                 Machine.next sign st
           | _ => NONE
        end

      fun safeEval sign st =
        case safeStep sign st of
           NONE => st
         | SOME st' => safeEval sign st'

      fun safeUnfold sign opid m =
        case out m of
           O.POLY (O.CUST (opid',_,_)) $ _ =>
             if Sym.eq (opid, opid') then
               Machine.unload sign (Option.valOf (safeStep sign (Machine.load m)))
                 handle _ => raise Fail "Impossible failure during safeUnfold" (* please put better error message here; should never happen anyway *)
             else
               m
         | _ => m
    end

    fun Unfold sign opid alpha jdg =
      let
        val _ = RedPrlLog.trace "Computation.Unfold"
        val unfold = safeUnfold sign opid o Abt.deepMapSubterms (safeUnfold sign opid)
        val jdg' = RedPrlSequent.map unfold jdg
        val (goal, hole) = makeGoal @@ ([],[]) || jdg'
      in
        T.empty >: goal #> hole [] []
      end

    fun EqHeadExpansion sign alpha jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqHeadExpansion"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Abt.$ (theta, _) = Abt.out m
        val m' = Machine.unload sign (safeEval sign (Machine.load m))
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ ((m', n), ty)
      in
        T.empty >: goal
          #> trivial
      end

    fun EqTypeHeadExpansion sign alpha jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqTypeHeadExpansion"
        val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
        val Abt.$ (theta, _) = Abt.out ty1
        val ty1' = Machine.unload sign (safeEval sign (Machine.load ty1))
        val (goal, _) = makeGoal @@ ([],[]) || (I, H) >> CJ.EQ_TYPE (ty1', ty2)
        in
          T.empty >: goal
            #> trivial
        end
  end

  fun Cut catjdg alpha jdg =
    let
      val _ = RedPrlLog.trace "Cut"
      val (I, H) >> catjdg' = jdg
      val z = alpha 0
      val tau = CJ.synthesis catjdg
      val (goal1, hole1) = makeGoal @@ ([], [(z, tau)]) || (I, H @> (z, catjdg)) >> catjdg'
      val (goal2, hole2) = makeGoal @@ ([],[]) || (I, H) >> catjdg
    in
      T.empty >: goal1 >: goal2
        #> hole1 [] [hole2 [] []]
    end


  local
    fun checkHyp H x jdg0 =
      case Hyps.find H x of
         SOME jdg =>
           if CJ.eq (jdg, jdg0) then () else
             raise E.error [E.% ("Hypothesis " ^ Sym.toString x ^ " did not match specification")]
       | _ => raise E.error [E.% ("Could not find hypothesis " ^ Sym.toString x)]

    fun checkMainGoal (specGoal, mainGoal) =
      let
        val (I, H) >> jdg = mainGoal
        val (J, H0) >> jdg0 = specGoal
      in
        if CJ.eq (jdg, jdg0) then () else raise E.error [E.% "Conclusions of goal did not match specification"];
        Hyps.foldl (fn (x, j, _) => checkHyp H x j) () H0
        (* TODO: unify using I, J!! *)
      end

    datatype diff =
       DELETE of hyp
     | UPDATE of hyp * catjdg
     | INSERT of hyp * catjdg

    val diffToString =
      fn DELETE x => "DELETE " ^ Sym.toString x
       | UPDATE (x,_) => "UPDATE " ^ Sym.toString x
       | INSERT (x,_) => "INSERT " ^ Sym.toString x


    fun applyDiff (delta : diff) (H : catjdg Hyps.telescope) : catjdg Hyps.telescope =
      case delta of
         DELETE x => Hyps.remove x H
       | UPDATE (x, jdg) => Hyps.modify x (fn _ => jdg) H
       | INSERT (x, jdg) => Hyps.snoc H x jdg

    fun applyDiffs (delta : diff list) : catjdg Hyps.telescope -> catjdg Hyps.telescope =
      List.foldl (fn (d, f) => applyDiff d o f) (fn H => H) delta

    fun hypothesesDiff (H0, H1) : diff list =
      let
        val diff01 =
          Hyps.foldr
            (fn (x, jdg0, delta) =>
              case Hyps.find H1 x of
                  SOME jdg1 => if CJ.eq (jdg0, jdg1) then delta else UPDATE (x, jdg1) :: delta
                | NONE => DELETE x :: delta)
            []
            H0
      in
        Hyps.foldr
          (fn (x, jdg1, delta) =>
             case Hyps.find H0 x of
                SOME jdg0 => delta
              | NONE => INSERT (x, jdg1) :: delta)
          diff01
          H1
      end

    fun instantiateSubgoal alpha (I, H) (subgoalSpec, mainGoalSpec) =
      let
        val Lcf.|| ((syms, vars), (I0, H0) >> jdg0) = subgoalSpec

        val nsyms = List.length syms
        val nvars = List.length vars

        val freshSyms = List.tabulate (nsyms, fn i => alpha i)
        val freshVars = List.tabulate (nvars, fn i => alpha (i + nsyms))

        val syms' = ListPair.map (fn ((u,sigma), v) => (v, sigma)) (syms, freshSyms)
        val vars' = ListPair.map (fn ((x, tau), y) => (y, tau)) (vars, freshVars)

        val hypren = ListPair.foldl (fn ((x, _), y, rho) => Sym.Ctx.insert rho x y) Sym.Ctx.empty (vars, freshVars)
        val srho = ListPair.foldl (fn ((u, _), v, rho) => Sym.Ctx.insert rho u (P.ret v)) Sym.Ctx.empty (syms, freshSyms)

        val bs = (syms', vars')

        val (I1, H1) >> jdg1 = mainGoalSpec
        val delta = hypothesesDiff (H1, H0)
        val H0' = applyDiffs delta H

        val jdg' = (I0, H0') >> jdg0
        val jdg'' = RedPrlSequent.map (substSymenv srho) (RedPrlSequent.relabel hypren jdg')
      in
        Lcf.|| (bs, jdg'')
      end
  in
    fun Lemma sign opid params args alpha jdg =
      let
        val _ = RedPrlLog.trace "Lemma"
        val (mainGoalSpec, state as Lcf.|> (subgoals, validation)) = Sig.resuscitateTheorem sign opid params args
        val _ = checkMainGoal (mainGoalSpec, jdg)

        val (I, H) >> _ = jdg

        val subgoals' = Lcf.Tl.map (fn subgoalSpec => instantiateSubgoal alpha (I, H) (subgoalSpec, mainGoalSpec)) subgoals
      in
        Lcf.|> (subgoals', validation)
      end
  end

  local
    fun matchGoal f alpha jdg =
      f jdg alpha jdg
  in
    local
      fun StepTrue sign ty =
        case Syn.out ty of
           Syn.PATH_TY _ => Path.True
         | Syn.DFUN _ => DFun.True
         | Syn.DPROD _ => DProd.True
         | _ => raise E.error [E.% "Could not find introduction rule for", E.! ty]

      fun StepEqTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Bool.EqType
         | (Syn.S_BOOL, Syn.S_BOOL) => StrictBool.EqType
         | (Syn.S1, Syn.S1) => S1.EqType
         | (Syn.DFUN _, Syn.DFUN _) => DFun.EqType
         | (Syn.DPROD _, Syn.DPROD _) => DProd.EqType
         | (Syn.PATH_TY _, Syn.PATH_TY _) => Path.EqType
         | _ => raise E.error [E.% "Could not find type equality rule for", E.! ty1, E.% "and", E.! ty2]

      fun StepEqType sign (ty1, ty2) =
        case (Machine.canonicity sign ty1, Machine.canonicity sign ty2) of
           (Machine.CANONICAL, Machine.CANONICAL) => StepEqTypeVal (ty1, ty2)
         | (Machine.REDEX, _) => Computation.EqTypeHeadExpansion sign
         | (_, Machine.REDEX) => TypeEquality.Symmetry
         | _ => raise E.error [E.% "Could not find type equality rule for", E.! ty1, E.% "and", E.! ty2]

      (* equality of canonical forms *)
      fun StepEqVal ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.TT, Syn.TT, Syn.BOOL) => Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Bool.EqFF
         | (Syn.FHCOM _, Syn.FHCOM _, Syn.BOOL) => FHCom.AutoEq
         | (Syn.TT, Syn.TT, Syn.S_BOOL) => StrictBool.EqTT
         | (Syn.FF, Syn.FF, Syn.S_BOOL) => StrictBool.EqFF
         | (Syn.BASE, Syn.BASE, Syn.S1) => S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => S1.EqLoop
         | (Syn.FHCOM _, Syn.FHCOM _, Syn.S1) => FHCom.AutoEq
         | (Syn.LAM _, Syn.LAM _, _) => DFun.Eq
         | (Syn.PAIR _, Syn.PAIR _, _) => DProd.Eq
         | (Syn.PATH_ABS _, Syn.PATH_ABS _, _) => Path.Eq
         | _ => raise E.error [E.% "Could not find value equality rule for", E.! m, E.% "and", E.! n, E.% "at type", E.! ty]

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeu (x, y) ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.VAR _, Syn.VAR _, _) => Equality.Hyp
         | (Syn.IF _, Syn.IF _, _) => Bool.ElimEq
         | (Syn.S_IF _, Syn.S_IF _, _) => StrictBool.ElimEq
         | (Syn.S_IF _, _, _) =>
           (case x of
               Machine.VAR z => StrictBool.EqElim z
             | _ => raise E.error [E.% "Could not determine critical variable at which to apply sbool elimination"])
         | (_, Syn.S_IF _, _) => Equality.Symmetry
         | (Syn.S1_ELIM _, Syn.S1_ELIM _, _) => S1.ElimEq
         | (Syn.AP _, Syn.AP _, _) => DFun.ApEq
         | (Syn.FST _, Syn.FST _, _) => DProd.FstEq
         | (Syn.SND _, Syn.SND _, _) => DProd.SndEq
         | (Syn.PATH_AP (_, P.VAR _), Syn.PATH_AP (_, P.VAR _), _) => Path.ApEq
         | (Syn.PATH_AP (_, P.APP _), _, _) => Path.ApComputeConst
         | (_, Syn.PATH_AP (_, P.APP _), _) => Equality.Symmetry
         | _ => raise E.error [E.% "Could not find neutral equality rule for", E.! m, E.% "and", E.! n, E.% "at type", E.! ty]

      fun StepEqEta ty =
        case Syn.out ty of
           Syn.DPROD _ => DProd.Eta
         | Syn.DFUN _ => DFun.Eta
         | Syn.PATH_TY _ => Path.Eta
         | _ => raise E.error [E.% "Could not find eta expansion rule for type", E.! ty]

      fun StepEqCanonicity sign ((m, n), ty) =
        case (Machine.canonicity sign m, Machine.canonicity sign n) of
           (Machine.CANONICAL, Machine.CANONICAL) => StepEqVal ((m, n), ty)
         | (Machine.NEUTRAL x, Machine.NEUTRAL y) => StepEqNeu (x, y) ((m, n), ty)
         | (Machine.REDEX, _) => Computation.EqHeadExpansion sign
         | (_, Machine.REDEX) => Equality.Symmetry
         | (Machine.NEUTRAL _, Machine.CANONICAL) => StepEqEta ty
         | (Machine.CANONICAL, Machine.NEUTRAL _) => Equality.Symmetry

      fun StepEq sign ((m, n), ty) =
        case (Syn.out m, Syn.out n) of
           (Syn.HCOM _, _) => HCom.AutoEq
         | (_, Syn.HCOM _) => Equality.Symmetry
         | (Syn.COE _, _) => Coe.AutoEq
         | (_, Syn.COE _) => Equality.Symmetry
         | _ => StepEqCanonicity sign ((m, n), ty)

      fun StepSynth sign m =
        case Syn.out m of
           Syn.VAR _ => Synth.Hyp
         | Syn.AP _ => Synth.Ap
         | Syn.S1_ELIM _ => Synth.S1Elim
         | Syn.IF _ => Synth.If
         | Syn.PATH_AP _ => Synth.PathAp
         | Syn.FST _ => Synth.Fst
         | Syn.SND _ => Synth.Snd
         | _ => raise E.error [E.% "Could not find suitable type synthesis rule for", E.! m]

      fun StepJdg sign = matchGoal
        (fn _ >> CJ.TRUE ty => StepTrue sign ty
          | _ >> CJ.EQ_TYPE tys => StepEqType sign tys
          | _ >> CJ.TYPE ty => Type.Intro
          | _ >> CJ.MEM _ => Membership.Intro
          | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
          | _ >> CJ.SYNTH m => StepSynth sign m
          | MATCH _ => Match.MatchOperator
          | jdg => raise E.error [E.% ("Could not find suitable rule for " ^ Seq.toString TermPrinter.toString jdg)])


      fun isWfJdg (CJ.TRUE _) = false
        | isWfJdg _ = true

      structure HypsUtil = TelescopeUtil (Hyps)

      fun FindHyp alpha ((I, H) >> jdg) =
        if isWfJdg jdg then
          case HypsUtil.search H (fn jdg' => CJ.eq (jdg, jdg')) of
             SOME (lbl, _) => Hyp.Project lbl alpha ((I, H) >> jdg)
           | NONE => raise E.error [E.% "Could not find suitable hypothesis"]
        else
          raise E.error [E.% "Non-deterministic tactics can only be run on auxiliary goals"]
    in
      fun AutoStep sign = orelse_ (StepJdg sign, FindHyp)
    end

    local
      fun StepTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.S_BOOL => StrictBool.Elim
         | Syn.S1 => S1.Elim
         | Syn.DFUN _ => DFun.Elim
         | Syn.DPROD _ => DProd.Elim
         | _ => raise E.error [E.% "Could not find suitable elimination rule for", E.! ty]

      fun StepEq ty =
        case Syn.out ty of
           Syn.S_BOOL => StrictBool.EqElim
         | _ => raise E.error [E.% "Could not find suitable elimination rule for", E.! ty]

      fun StepJdg sign z alpha jdg =
        let
          val (I, H) >> catjdg = jdg
        in
          case lookupHyp H z of
             CJ.TRUE hyp =>
              (case catjdg of
                  CJ.TRUE _ => StepTrue hyp z alpha jdg
                | CJ.EQ _ => StepEq hyp z alpha jdg
                | _ => raise E.error [E.% ("Could not find suitable elimination rule for " ^ CJ.toString catjdg)])
           | CJ.TYPE _ => Type.Elim z alpha jdg
           | _ => raise E.error [E.% "Could not find suitable elimination rule"]
        end
    in
      val Elim = StepJdg
    end

  end
end
