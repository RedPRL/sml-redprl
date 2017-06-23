(* type-specific modules *)
functor RefinerTypeRules (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  open RedPrlAbt Kit ComRefinerKit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = abt CJ.jdg
  type opid = Sig.opid

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:+ $$ $# // \ @>
  infix orelse_

  structure Bool =
  struct
    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqType"
        val (I, H) >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
      in
        T.empty #> (I, H, trivial)
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
        T.empty #> (I, H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.BOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "EqFCom"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.BOOL = Syn.out ty
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs
      in
        ComKit.EqFComDelegator alpha (I, H) args0 args1 ty
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.BOOL = Syn.out ty

        val tt = Syn.into Syn.TT
        val ff = Syn.into Syn.FF

        val (goalT, holeT) = makeGoal @@ (I, Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H) >> CJ.TRUE (substVar (tt, z) cz)
        val (goalF, holeF) = makeGoal @@ (I, Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H) >> CJ.TRUE (substVar (ff, z) cz)

        val psi = T.empty >: goalT >: goalF
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val if_ = Syn.into @@ Syn.IF ((z, cz), ztm, (holeT, holeF))
      in
        psi #> (I, H, if_)
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

        val (goalTy, _) = makeGoal @@ (I, H @> (z, CJ.TRUE @@ Syn.into Syn.BOOL)) >> CJ.EQ_TYPE (c0z, c1z)
        val (goalTy', _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (c0m0, c)
        val (goalM, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), Syn.into Syn.BOOL)
        val (goalT, _) = makeGoal @@ (I, H) >> CJ.EQ ((t0, t1), c0tt)
        val (goalF, _) = makeGoal @@ (I, H) >> CJ.EQ ((f0, f1), c0ff)
        val psi = T.empty >: goalTy >: goalM >: goalT >: goalF
      in
        psi #> (I, H, trivial)
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
        T.empty #> (I, H, trivial)
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
        T.empty #> (I, H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.S_BOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.S_BOOL = Syn.out ty

        val tt = Syn.into Syn.TT
        val ff = Syn.into Syn.FF

        val (goalT, holeT) = makeGoal @@ (I, Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H) >> CJ.TRUE (substVar (tt, z) cz)
        val (goalF, holeF) = makeGoal @@ (I, Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H) >> CJ.TRUE (substVar (ff, z) cz)

        val psi = T.empty >: goalT >: goalF
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val if_ = Syn.into @@ Syn.S_IF (ztm, (holeT, holeF))
      in
        psi #> (I, H, if_)
      end
      handle Bind =>
        raise E.error [E.% "Expected strict bool elimination problem"]

    fun ElimEq alpha jdg =
      let
        val _ = RedPrlLog.trace "StrictBool.ElimEq"
        val (I, H) >> CJ.EQ ((if0, if1), c) = jdg
        val Syn.S_IF (m0, (t0, f0)) = Syn.out if0
        val Syn.S_IF (m1, (t1, f1)) = Syn.out if1

        val (goalM, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), Syn.into Syn.S_BOOL)
        val (goalT, _) = makeGoal @@ (I, H) >> CJ.EQ ((t0, t1), c)
        val (goalF, _) = makeGoal @@ (I, H) >> CJ.EQ ((f0, f1), c)
        val psi = T.empty >: goalM >: goalT >: goalF
      in
        psi #> (I, H, trivial)
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

        val (goalM0, _) = makeGoal @@ (I, H) >> CJ.MEM (m0z, cz)
        val (goalM1, _) = makeGoal @@ (I, H) >> CJ.MEM (m1z, cz)
        val (goalT, _) = makeGoal @@ (I, Hyps.modifyAfter z (CJ.map (substVar (tt, z))) H) >> CJ.map (substVar (tt, z)) catjdg
        val (goalF, _) = makeGoal @@ (I, Hyps.modifyAfter z (CJ.map (substVar (ff, z))) H) >> CJ.map (substVar (ff, z)) catjdg

        val psi = T.empty >: goalM0 >: goalM1 >: goalT >: goalF
      in
        psi #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [E.% "Expected strict bool elimination problem"]
  end

  structure Void =
  struct
    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Void.EqType"
        val (I, H) >> CJ.EQ_TYPE (a, b) = jdg
        val Syn.VOID = Syn.out a
        val Syn.VOID = Syn.out b
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [E.% "Expected typehood sequent"]

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Void.Elim"
        val (I, H) >> catjdg = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.VOID = Syn.out ty

        val evidence =
          case catjdg of
             CJ.TRUE _ => Syn.into Syn.TT
           | CJ.EQ _ => trivial
           | CJ.EQ_TYPE _ => trivial
           | _ => raise Fail "Void.Elim cannot be called with this kind of goal"
      in
        T.empty #> (I, H, evidence)
      end
      handle Bind =>
        raise E.error [E.% "Expected Void elimination problem"]
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
        T.empty #> (I, H, trivial)
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
        T.empty #> (I, H, trivial)
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
        T.empty #> (I, H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "EqFCom"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.S1 = Syn.out ty
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs
      in
        ComKit.EqFComDelegator alpha (I, H) args0 args1 ty
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE ty = lookupHyp H z
        val Syn.S1 = Syn.out ty

        val u = alpha 0
        val base = Syn.into Syn.BASE
        val loop = Syn.into o Syn.LOOP @@ P.ret u
        val Hbase = Hyps.modifyAfter z (CJ.map (substVar (base, z))) H
        val cbase = substVar (base, z) cz

        val (goalB, holeB) = makeGoal @@ (I, Hbase) >> CJ.TRUE cbase
        val (goalL, holeL) = makeGoal @@ (I @ [(u, P.DIM)], Hyps.modifyAfter z (CJ.map (substVar (loop, z))) H) >> CJ.TRUE (substVar (loop, z) cz)

        val l0 = substSymbol (P.APP P.DIM0, u) holeL
        val l1 = substSymbol (P.APP P.DIM1, u) holeL

        val (goalCoh0, _) = makeGoal @@ (I, Hbase) >> CJ.EQ ((l0, holeB), cbase)
        val (goalCoh1, _) = makeGoal @@ (I, Hbase) >> CJ.EQ ((l1, holeB), cbase)

        val psi = T.empty >: goalB >: goalL >: goalCoh0 >: goalCoh1

        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val elim = Syn.into @@ Syn.S1_ELIM ((z, cz), ztm, (holeB, (u, holeL)))
      in
        psi #> (I, H, elim)
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

        val (goalCz, _) = makeGoal @@ (I, H @> (z, CJ.TRUE S1)) >> CJ.EQ_TYPE (c0z, c1z)
        val (goalM, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), S1)
        val (goalB, _) = makeGoal @@ (I, H) >> CJ.EQ ((b0, b1), cbase)
        val (goalL, _) = makeGoal @@ (I, H) >> CJ.EQ ((l0u, l1u), cloop)
        val (goalL00, _) = makeGoal @@ (I, H) >> CJ.EQ ((l00, b0), cbase)
        val (goalL01, _) = makeGoal @@ (I, H) >> CJ.EQ ((l01, b0), cbase)

        val psi = T.empty >: goalCz >: goalM >: goalB >: goalL >: goalL00 >: goalL01
      in
        psi #> (I, H, trivial)
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

        val (goal1, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (a0, a1)
        val (goal2, _) = makeGoal @@ (I, H @> (z, CJ.TRUE a0)) >> CJ.EQ_TYPE (b0z, b1z)
      in
        T.empty >: goal1 >: goal2
          #> (I, H, trivial)
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

        val (goal1, _) = makeGoal @@ (I, H @> (w, CJ.TRUE a)) >> CJ.EQ ((m0w, m1w), bw)
        val (goal2, _) = makeGoal @@ (I, H) >> CJ.TYPE a
      in
        T.empty >: goal1 >: goal2
          #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.True"
        val (I, H) >> CJ.TRUE dfun = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val bz = substVar (ztm, x) bx

        val (tyGoal, _) = makeGoal @@ (I, H) >> CJ.TYPE a
        val (goal, hole) = makeGoal @@ (I, H @> (z, CJ.TRUE a)) >> CJ.TRUE bz

        val psi = T.empty >: goal >: tyGoal
        val lam = Syn.into @@ Syn.LAM (z, substVar (ztm, z) hole)
      in
        psi #> (I, H, lam)
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
        val (goal1, _) = makeGoal @@ (I, H) >> CJ.MEM (m, dfun)
        val (goal2, _) = makeGoal @@ (I, H) >> CJ.EQ ((m', n), dfun)
      in
        T.empty >: goal1 >: goal2
          #> (I, H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Elim"
        val (I, H) >> CJ.TRUE cz = jdg
        val CJ.TRUE dfun = Hyps.lookup H z
        val Syn.DFUN (a, x, bx) = Syn.out dfun
        val (goal1, hole1) = makeGoal @@ (I, H) >> CJ.TRUE a

        val u = alpha 0
        val v = alpha 1

        val b' = substVar (hole1, x) bx

        val utm = Syn.into @@ Syn.VAR (u, O.EXP)
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val aptm = Syn.into @@ Syn.AP (ztm, hole1)
        val H' = Hyps.empty @> (u, CJ.TRUE b') @> (v, CJ.EQ ((utm, aptm), b'))
        val H'' = Hyps.interposeAfter H z H'

        val (goal2, hole2) = makeGoal @@ (I, H'') >> CJ.TRUE cz

        val psi = T.empty >: goal1 >: goal2
        val aptm = Syn.into @@ Syn.AP (ztm, hole1)
        val rho = Var.Ctx.insert (Var.Ctx.insert Var.Ctx.empty u aptm) v (Syn.into Syn.AX)
        val hole2' = substVarenv rho hole2
      in
        psi #> (I, H, hole2')
      end

    fun ApEq alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.ApEq"
        val (I, H) >> CJ.EQ ((ap0, ap1), c) = jdg
        val Syn.AP (m0, n0) = Syn.out ap0
        val Syn.AP (m1, n1) = Syn.out ap1

        val (goalDFun0, holeDFun0) = makeGoal @@ (I, H) >> CJ.SYNTH m0
        val (goalDFun1, holeDFun1) = makeGoal @@ (I, H) >> CJ.SYNTH m1
        val (goalDFunEq, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (holeDFun0, holeDFun1)
        val (goalDom, holeDom) = makeGoal @@ MATCH (O.MONO O.DFUN, 0, holeDFun0, [], [])
        val (goalM, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), holeDFun0)
        val (goalN, _) = makeGoal @@ (I, H) >> CJ.EQ ((n0, n1), holeDom)
      in
        T.empty >: goalDFun0 >: goalDFun1 >: goalDFunEq >: goalDom >: goalM >: goalN
          #> (I, H, trivial)
      end
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

        val (goal1, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (a0, a1)
        val (goal2, _) = makeGoal @@ (I, H @> (z, CJ.TRUE a0)) >> CJ.EQ_TYPE (b0z, b1z)
      in
        T.empty >: goal1 >: goal2
          #> (I, H, trivial)
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

        val (goal1, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), a)
        val (goal2, _) = makeGoal @@ (I, H) >> CJ.EQ ((n0, n1), substVar (m0, x) bx)
        val (goalFam, _) = makeGoal @@ (I, H @> (z, CJ.TRUE a)) >> CJ.TYPE bz
      in
        T.empty >: goal1 >: goal2 >: goalFam
          #> (I, H, trivial)
      end

    fun Eta alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.Eta"
        val (I, H) >> CJ.EQ ((m, n), dprod) = jdg
        val Syn.DPROD (a, x, bx) = Syn.out dprod

        val m' = Syn.into @@ Syn.PAIR (Syn.into @@ Syn.FST m, Syn.into @@ Syn.SND m)
        val (goal1, _) = makeGoal @@ (I, H) >> CJ.MEM (m, dprod)
        val (goal2, _) = makeGoal @@ (I, H) >> CJ.EQ ((m', n), dprod)
      in
        T.empty >: goal1 >: goal2
          #> (I, H, trivial)
      end

    fun FstEq alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.FstEq"
        val (I, H) >> CJ.EQ ((fst0, fst1), ty) = jdg
        val Syn.FST m0 = Syn.out fst0
        val Syn.FST m1 = Syn.out fst1

        val (goalTy, holeTy) = makeGoal @@ (I, H) >> CJ.SYNTH m0
        val (goalTyA, holeTyA) = makeGoal @@ MATCH (O.MONO O.DPROD, 0, holeTy, [], [])
        val (goalEq, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), holeTy)
        val (goalEqTy, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (holeTyA, ty)
      in
        T.empty >: goalTy >: goalTyA >: goalEq >: goalEqTy
          #> (I, H, trivial)
      end

    fun SndEq alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.SndEq"
        val (I, H) >> CJ.EQ ((snd0, snd1), ty) = jdg
        val Syn.SND m0 = Syn.out snd0
        val Syn.SND m1 = Syn.out snd1

        val (goalTy, holeTy) = makeGoal @@ (I, H) >> CJ.SYNTH m0
        val (goalTyB, holeTyB) = makeGoal @@ MATCH (O.MONO O.DPROD, 1, holeTy, [], [Syn.into @@ Syn.FST m0])
        val (goalEq, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), holeTy)
        val (goalEqTy, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (holeTyB, ty)
      in
        T.empty >: goalTy >: goalTyB >: goalEq >: goalEqTy
          #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "DProd.True"
        val (I, H) >> CJ.TRUE dprod = jdg
        val Syn.DPROD (a, x, bx) = Syn.out dprod

        val z = alpha 0
        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val bz = substVar (ztm, x) bx

        val (goal1, hole1) = makeGoal @@ (I, H) >> CJ.TRUE a
        val (goal2, hole2) = makeGoal @@ (I, H) >> CJ.TRUE (substVar (hole1, x) bx)
        val (goalFam, _) = makeGoal @@ (I, H @> (z, CJ.TRUE a)) >> CJ.TYPE bz
        val psi = T.empty >: goal1 >: goal2 >: goalFam
        val pair = Syn.into @@ Syn.PAIR (hole1, hole2)
      in
        psi #> (I, H, pair)
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
            @@ (I, Hyps.modifyAfter z (CJ.map (substVar (pair, z))) H'')
            >> CJ.TRUE (substVar (pair, z) cz)

        val psi = T.empty >: goal

        val ztm = Syn.into @@ Syn.VAR (z, O.EXP)
        val fstz = Syn.into @@ Syn.FST ztm
        val sndz = Syn.into @@ Syn.SND ztm
        val rho = Var.Ctx.insert (Var.Ctx.insert Var.Ctx.empty z1 fstz) z2 sndz
        val hole' = substVarenv rho hole
      in
        T.empty >: goal
          #> (I, H, hole')
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

        val (tyGoal, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (a0u, a1u)
        val (goal0, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), a00)
        val (goal1, _) = makeGoal @@ (I, H) >> CJ.EQ ((n0, n1), a01)
      in
        T.empty >: tyGoal >: goal0 >: goal1
          #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.True"
        val (I, H) >> CJ.TRUE ty = jdg
        val Syn.PATH_TY ((u, a), p0, p1) = Syn.out ty
        val a0 = substSymbol (P.APP P.DIM0, u) a
        val a1 = substSymbol (P.APP P.DIM1, u) a

        val v = alpha 0

        val (mainGoal, mhole) = makeGoal @@ (I @ [(v, P.DIM)], H) >> CJ.TRUE (substSymbol (P.ret v, u) a)

        val m0 = substSymbol (P.APP P.DIM0, v) mhole
        val m1 = substSymbol (P.APP P.DIM1, v) mhole
        val (cohGoal0, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, p0), a0)
        val (cohGoal1, _) = makeGoal @@ (I, H) >> CJ.EQ ((m1, p1), a1)

        val psi = T.empty >: mainGoal >: cohGoal0 >: cohGoal1
        val abstr = Syn.into @@ Syn.PATH_ABS (v, mhole)
      in
        psi #> (I, H, abstr)
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

        val (goalM, _) = makeGoal @@ (I @ [(z, P.DIM)], H) >> CJ.EQ ((m0z, m1z), az)
        val (goalM00, _) = makeGoal @@ (I, H) >> CJ.EQ ((m00, p0), a0)
        val (goalM01, _) = makeGoal @@ (I, H) >> CJ.EQ ((m01, p1), a1)
      in
        T.empty >: goalM >: goalM00 >: goalM01
          #> (I, H, trivial)
      end

    fun ApEq alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.ApEq"
        val (I, H) >> CJ.EQ ((ap0, ap1), ty) = jdg
        val Syn.PATH_AP (m0, r0) = Syn.out ap0
        val Syn.PATH_AP (m1, r1) = Syn.out ap1
        val () = assertParamEq "Path.ApEq" (r0, r1)
        val (goalSynth, holeSynth) = makeGoal @@ (I, H) >> CJ.SYNTH m0
        val (goalMem, _) = makeGoal @@ (I, H) >> CJ.EQ ((m0, m1), holeSynth)
        val (goalLine, holeLine) = makeGoal @@ MATCH (O.MONO O.PATH_TY, 0, holeSynth, [r0], [])
        val (goalTy, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty, holeLine)
      in
        T.empty >: goalSynth >: goalMem >: goalLine >: goalTy
          #> (I, H, trivial)
      end

    fun ApConstCompute alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.ApConstCompute"
        val (I, H) >> CJ.EQ ((ap, p), a) = jdg
        val Syn.PATH_AP (m, P.APP r) = Syn.out ap
        val (goalSynth, holeSynth) = makeGoal @@ (I, H) >> CJ.SYNTH m

        val dimAddr = case r of P.DIM0 => 1 | P.DIM1 => 2
        val (goalLine, holeLine) = makeGoal @@ MATCH (O.MONO O.PATH_TY, 0, holeSynth, [P.APP r], [])
        val (goalEndpoint, holeEndpoint) = makeGoal @@ MATCH (O.MONO O.PATH_TY, dimAddr, holeSynth, [], [])
        val (goalTy, _) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (a, holeLine)
        val (goalEq, _) = makeGoal @@ (I, H) >> CJ.EQ ((holeEndpoint, p), a)
      in
        T.empty >: goalSynth >: goalLine >: goalEndpoint >: goalTy >: goalEq
          #> (I, H, trivial)
      end

    fun Eta alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.Eta"
        val (I, H) >> CJ.EQ ((m, n), pathTy) = jdg
        val Syn.PATH_TY ((u, a), p0, p1) = Syn.out pathTy

        val m' = Syn.into @@ Syn.PATH_ABS (u, Syn.into @@ Syn.PATH_AP (m, P.ret u))
        val (goal1, _) = makeGoal @@ (I, H) >> CJ.MEM (m, pathTy)
        val (goal2, _) = makeGoal @@ (I, H) >> CJ.EQ ((m', n), pathTy)
      in
        T.empty >: goal1 >: goal2
          #> (I, H, trivial)
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
          T.empty #> (I, H, Syn.into (Syn.VAR (z, CJ.synthesis catjdg)))
        else
          raise E.error [E.% "Hypothesis does not match goal"]
      end
      handle Bind =>
        raise E.error [E.% "Expected sequent judgment"]
  end

  structure TypeEquality =
  struct
    fun Symmetry alpha jdg =
    let
      val _ = RedPrlLog.trace "Equality.Symmetry"
      val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
      val (goal, hole) = makeGoal @@ (I, H) >> CJ.EQ_TYPE (ty2, ty1)
    in
      T.empty >: goal
        #> (I, H, trivial)
    end
  end

  structure Truth =
  struct
    fun Witness tm alpha jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> CJ.TRUE ty = jdg
        val (goal, _) = makeGoal @@ (I, H) >> CJ.MEM (tm, ty)
      in
        T.empty >: goal
          #> (I, H, tm)
      end
      handle Bind =>
        raise E.error [E.% @@ "Expected truth sequent but got " ^ J.toString jdg]
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
          T.empty #> (I, H, ty)
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
        T.empty #> (I, H, a)
      end

    fun Ap alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Ap"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.AP (m, n) = Syn.out tm
        val (goalDFun, holeDFun) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalDom, holeDom) = makeGoal @@ MATCH (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeGoal @@ MATCH (O.MONO O.DFUN, 1, holeDFun, [], [n])
        val (goalN, _) = makeGoal @@ (I, H) >> CJ.MEM (n, holeDom)
      in
        T.empty >: goalDFun >: goalDom >: goalCod >: goalN
          #> (I, H, holeCod)
      end

    fun S1Elim alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.S1Elim"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.S1_ELIM ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val (goal, _) = makeGoal @@ (I, H) >> CJ.MEM (tm, cm)
      in
        T.empty >: goal
          #> (I, H, cm)
      end

    fun If alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.If"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.IF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val (goal, _) = makeGoal @@ (I, H) >> CJ.MEM (tm, cm)
      in
        T.empty >: goal
          #> (I, H, cm)
      end

    fun PathAp alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.PathAp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.PATH_AP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalLine, holeLine) = makeGoal @@ MATCH (O.MONO O.PATH_TY, 0, holePathTy, [r], [])
        val psi = T.empty >: goalPathTy >: goalLine
      in
        T.empty >: goalPathTy >: goalLine
          #> (I, H, holeLine)
      end

    fun Fst alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Fst"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.FST m = Syn.out tm
        val (goalTy, holeTy) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalA, holeA) = makeGoal @@ MATCH (O.MONO O.DPROD, 0, holeTy, [], [])
      in
        T.empty >: goalTy >: goalA
          #> (I, H, holeA)
      end

    fun Snd alpha jdg =
      let
        val _ = RedPrlLog.trace "Synth.Snd"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.SND m = Syn.out tm
        val (goalTy, holeTy) = makeGoal @@ (I, H) >> CJ.SYNTH m
        val (goalB, holeB) = makeGoal @@ MATCH (O.MONO O.DPROD, 1, holeTy, [], [Syn.into @@ Syn.FST m])
      in
        T.empty >: goalTy >: goalB
          #> (I, H, holeB)
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
        Lcf.|> (T.empty, abtToAbs arg')
      end
      handle _ =>
        raise E.error [E.% "MATCH judgment failed to unify"]
  end
end
