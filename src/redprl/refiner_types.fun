(* type-specific modules *)
functor RefinerTypeRules (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  open RedPrlAbt Kit ComRefinerKit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = CJ.jdg
  type opid = Sig.opid

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix orelse_

  (* Rules in a type should be ordered as follows:
   *
   * EqType: the type formation rule.
   * EqX: the introduction rule for the constructor X of a positive type.
   * True: the introduction rule of a negative type.
   * Eta: the eta rule, if any.
   * Elim: the elimination rule. This should be in the strongest form we
   *   consider to be obviously true within the limit of RedPRL.
   * EqElim/EqX: structural equality for eliminators.
   *   We use EqX if the eliminator has a well-known name X.
   *   For example, we have EqApp for DFun and Path, and EqProj for Record.
   * (others): other special rules for this type.
   *)

  (* Remember to consult `alpha` whenever some goals introduce new hypotheses
   * or new parameter variables.
   *)

  structure Bool =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqTT"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.BOOL = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.BOOL = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.Elim"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.BOOL = Syn.out ty

        (* tt branch *)
        val tt = Syn.into Syn.TT
        val Htt = Hyps.substAfter (z, tt) H
        val (goalT, holeT) = makeGoal @@ (I, Htt) >> CJ.map (substVar (tt, z)) catjdg

        (* ff branch *)
        val ff = Syn.into Syn.FF
        val Hff = Hyps.substAfter (z, ff) H
        val (goalF, holeF) = makeGoal @@ (I, Hff) >> CJ.map (substVar (ff, z)) catjdg

        val evidence =
          case catjdg of
             CJ.TRUE _ => Syn.into @@ Syn.IF (VarKit.toExp z, (holeT, holeF))
           | CJ.EQ _ => trivial
           | CJ.EQ_TYPE _ => trivial
           | CJ.SYNTH _ => Syn.into @@ Syn.IF (VarKit.toExp z, (holeT, holeF))
           | _ => raise Fail "Bool.Elim cannot be called with this kind of goal"
      in
        |>: goalT >: goalF #> (I, H, evidence)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected strict bool elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqElim"
        val (I, H) >> CJ.EQ ((if0, if1), (ty, l, k)) = jdg
        val Syn.IF (m0, (t0, f0)) = Syn.out if0
        val Syn.IF (m1, (t1, f1)) = Syn.out if1

        (* motive *)
        val x = alpha 0
        val Hx = H @> (x, CJ.TRUE (Syn.into Syn.BOOL, SOME inherentLevel, inherentKind))
        val (goalTy, holeTy) = makeTerm (I, Hx) O.EXP
        val goalTy' = makeType (I, Hx) (holeTy, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (Syn.into Syn.BOOL, NONE, K.top))

        (* result type*)
        val goalTy0 = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((substVar (m0, x) holeTy, ty), l, k) (NONE, K.top)

        (* tt branch *)
        val goalT = makeEq (I, H) ((t0, t1), (substVar (Syn.into Syn.TT, x) holeTy, NONE, K.top))

        (* ff branch *)
        val goalF = makeEq (I, H) ((f0, f1), (substVar (Syn.into Syn.FF, x) holeTy, NONE, K.top))
      in
        |>: goalTy >: goalM >: goalT >: goalF >:? goalTy0 >: goalTy' #> (I, H, trivial)
      end
  end

  structure WBool =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.KAN

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.WBOOL = Syn.out a
        val Syn.WBOOL = Syn.out b
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqTT"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqFCom"
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs
      in
        ComKit.EqFComDelegate alpha (I, H) args0 args1 (ty, NONE, K.top)
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.Elim"
        val (I, H) >> CJ.TRUE (cz, l, k) = jdg
        (* if(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.WBOOL = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType (I, H) (cz, l, k)

        (* tt branch *)
        val (goalT, holeT) = makeTrue (I, H) (substVar (Syn.into Syn.TT, z) cz, NONE, K.top)

        (* ff branch *)
        val (goalF, holeF) = makeTrue (I, H) (substVar (Syn.into Syn.FF, z) cz, NONE, K.top)

        (* realizer *)
        val if_ = Syn.into @@ Syn.WIF ((z, cz), VarKit.toExp z, (holeT, holeF))
      in
        |>: goalT >: goalF >: goalKind #> (I, H, if_)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected bool elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqElim"
        val (I, H) >> CJ.EQ ((if0, if1), (ty, l, k)) = jdg
        (* if(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.WIF ((x, c0x), m0, (t0, f0)) = Syn.out if0
        val Syn.WIF ((y, c1y), m1, (t1, f1)) = Syn.out if1

        (* motive *)
        val z = alpha 0
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val Hz = H @> (z, CJ.TRUE (Syn.into Syn.WBOOL, SOME inherentLevel, inherentKind))
        val goalTy = makeEqType (I, Hz) ((c0z, c1z), NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (Syn.into Syn.WBOOL, NONE, K.top))

        (* result type*)
        val goalTy0 = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((substVar (m0, x) c0x, ty), l, k) (NONE, K.top)

        (* tt branch *)
        val goalT = makeEq (I, H) ((t0, t1), (substVar (Syn.into Syn.TT, x) c0x, NONE, K.top))

        (* ff branch *)
        val goalF = makeEq (I, H) ((f0, f1), (substVar (Syn.into Syn.FF, x) c0x, NONE, K.top))
      in
        |>: goalM >: goalT >: goalF >:? goalTy0 >: goalTy #> (I, H, trivial)
      end
  end

  structure Nat =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.NAT = Syn.out a
        val Syn.NAT = Syn.out b
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqZero"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.NAT = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqSucc"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.NAT = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq (I, H) ((m', n'), (Syn.into Syn.NAT, NONE, K.top))
      in
        |>: goal #> (I, H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.Elim"
        val (I, H) >> CJ.TRUE (cz, l, k) = jdg
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.NAT = Syn.out ty

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* zero branch *)
        val (goalZ, holeZ) = makeTrue (I, H) (substVar (zero, z) cz, l, k)

        (* succ branch *)
        val u = alpha 0
        val v = alpha 1
        val cu = VarKit.rename (u, z) cz
        val (goalS, holeS) =
          makeTrue
            (I, H @> (u, CJ.TRUE (nat, SOME inherentLevel, inherentKind)) @> (v, CJ.TRUE (cu, l, k)))
            (substVar (succ @@ VarKit.toExp u, z) cz, l, k)

        (* realizer *)
        val evidence = Syn.into @@ Syn.NAT_REC (VarKit.toExp z, (holeZ, (u, v, holeS)))
      in
        |>: goalZ >: goalS #> (I, H, evidence)
      end

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqElim"
        val (I, H) >> CJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        val Syn.NAT_REC (m0, (n0, (a0, b0, p0))) = Syn.out elim0
        val Syn.NAT_REC (m1, (n1, (a1, b1, p1))) = Syn.out elim1

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* motive *)
        val z = alpha 0
        val Hz = H @> (z, CJ.TRUE (nat, SOME inherentLevel, inherentKind))
        val (goalC, holeC) = makeTerm (I, Hz) O.EXP
        val goalC' = makeType (I, Hz) (holeC, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (nat, NONE, K.top))

        (* result type *)
        val goalTy = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((substVar (m0, z) holeC, ty), l, k) (NONE, K.top)

        (* zero branch *)
        val goalZ = makeEq (I, H) ((n0, n1), (substVar (zero, z) holeC, NONE, K.top))

        (* succ branch *)
        val u = alpha 1
        val v = alpha 2
        val cu = VarKit.rename (u, z) holeC
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            (I, H @> (u, CJ.TRUE (nat, SOME inherentLevel, inherentKind)) @> (v, CJ.TRUE (cu, l, k)))
            ((p0, p1), (substVar (succ @@ VarKit.toExp u, z) holeC, NONE, K.top))
      in
        |>: goalC >: goalM >: goalZ >: goalS >: goalC' >:? goalTy #> (I, H, trivial)
      end
  end

  structure Int =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.INT = Syn.out a
        val Syn.INT = Syn.out b
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqZero"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqSucc"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq (I, H) ((m', n'), (Syn.into Syn.NAT, NONE, K.top))
      in
        |>: goal #> (I, H, trivial)
      end

    fun EqNegSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqNegSucc"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.NEGSUCC m' = Syn.out m
        val Syn.NEGSUCC n' = Syn.out n
        val goal = makeEq (I, H) ((m', n'), (Syn.into Syn.NAT, NONE, K.top))
      in
        |>: goal #> (I, H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Int.Elim"
        val (I, H) >> CJ.TRUE (cz, l, k) = jdg
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.INT = Syn.out ty

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC
        val negsucc = Syn.into o Syn.NEGSUCC

        (* zero branch *)
        val (goalZ, holeZ) = makeTrue (I, H) (substVar (zero, z) cz, l, k)

        (* succ branch *)
        val u = alpha 0
        val v = alpha 1
        val cu = VarKit.rename (u, z) cz
        val (goalS, holeS) =
          makeTrue
            (I, H @> (u, CJ.TRUE (nat, SOME Nat.inherentLevel, Nat.inherentKind)) @> (v, CJ.TRUE (cu, l, k)))
            (substVar (succ @@ VarKit.toExp u, z) cz, l, k)

        (* (negsucc zero) branch *)
        val (goalNSZ, holeNSZ) = makeTrue (I, H) (substVar (negsucc zero, z) cz, l, k)

        (* (negsucc succ) branch *)
        val cnegsuccu = Abt.substVar (negsucc @@ VarKit.toExp u, z) cz
        val (goalNSS, holeNSS) =
          makeTrue
            (I, H @> (u, CJ.TRUE (nat, SOME Nat.inherentLevel, Nat.inherentKind)) @> (v, CJ.TRUE (cnegsuccu, l, k)))
            (substVar (negsucc @@ succ @@ VarKit.toExp u, z) cz, l, k)

        (* realizer *)
        val evidence = Syn.into @@ Syn.INT_REC (VarKit.toExp z, (holeZ, (u, v, holeS), holeNSZ, (u, v, holeNSS)))
      in
        |>: goalZ >: goalS >: goalNSZ >: goalNSS #> (I, H, evidence)
      end

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Int.EqElim"
        val (I, H) >> CJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        val Syn.INT_REC (m0, (n0, (a0, b0, p0), q0, (c0, d0, r0))) = Syn.out elim0
        val Syn.INT_REC (m1, (n1, (a1, b1, p1), q1, (c1, d1, r1))) = Syn.out elim1

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC
        val negsucc = Syn.into o Syn.NEGSUCC

        (* motive *)
        val z = alpha 0
        val Hz = H @> (z, CJ.TRUE (nat, SOME Nat.inherentLevel, Nat.inherentKind))
        val (goalC, holeC) = makeTerm (I, Hz) O.EXP
        val goalC' = makeType (I, Hz) (holeC, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (nat, NONE, K.top))

        (* result type *)
        val goalTy = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((substVar (m0, z) holeC, ty), l, k) (NONE, K.top)

        (* zero branch *)
        val goalZ = makeEq (I, H) ((n0, n1), (substVar (zero, z) holeC, NONE, K.top))

        (* succ branch *)
        val u = alpha 1
        val v = alpha 2
        val cu = VarKit.rename (u, z) holeC
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            (I, H @> (u, CJ.TRUE (nat, SOME Nat.inherentLevel, Nat.inherentKind)) @> (v, CJ.TRUE (cu, l, k)))
            ((p0, p1), (substVar (succ @@ VarKit.toExp u, z) holeC, NONE, K.top))

        (* (negsucc zero) branch *)
        val goalNSZ = makeEq (I, H) ((q0, q1), (substVar (negsucc zero, z) holeC, NONE, K.top))

        (* (negsucc succ) branch *)
        val cnegsuccu = Abt.substVar (negsucc @@ VarKit.toExp u, z) holeC
        val r0 = VarKit.renameMany [(u, c0), (v, d0)] r0
        val r1 = VarKit.renameMany [(u, c1), (v, d1)] r1
        val goalNSS =
          makeEq
            (I, H @> (u, CJ.TRUE (nat, l, inherentKind)) @> (v, CJ.TRUE (cnegsuccu, l, k)))
            ((r0, r1), (substVar (negsucc @@ succ @@ VarKit.toExp u, z) holeC, NONE, K.top))
      in
        |>: goalC >: goalM >: goalZ >: goalS >: goalNSZ >: goalNSS >: goalC' >:? goalTy #> (I, H, trivial)
      end
  end

  structure Void =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Void.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.VOID = Syn.out a
        val Syn.VOID = Syn.out b
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Void.Elim"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.VOID = Syn.out ty

        val evidence =
          case catjdg of
             CJ.TRUE _ => Syn.into Syn.AX (* should be some fancy symbol *)
           | CJ.EQ _ => trivial
           | CJ.EQ_TYPE _ => trivial
           | CJ.SYNTH _ => Syn.into Syn.AX
           | _ => raise Fail "Void.Elim cannot be called with this kind of goal"
      in
        T.empty #> (I, H, evidence)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected Void elimination problem"]
  end

  structure S1 =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.KAN

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.S1 = Syn.out a
        val Syn.S1 = Syn.out b
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqBase _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqBase"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.BASE = Syn.out m
        val Syn.BASE = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqLoop _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqLoop"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.LOOP r1 = Syn.out m
        val Syn.LOOP r2 = Syn.out n
        val () = Assert.paramEq "S1.EqLoop" (r1, r2)
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.EqFCom"
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.levelLeq (SOME inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs
      in
        ComKit.EqFComDelegate alpha (I, H) args0 args1 (ty, NONE, K.top)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.Elim"
        val (I, H) >> CJ.TRUE (cz, l, k) = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.S1 = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType (I, H) (cz, l, k)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, z) cz
        val (goalB, holeB) = makeTrue (I, H) (cbase, NONE, K.top)

        (* loop branch *)
        val u = alpha 0
        val loop = Syn.into o Syn.LOOP @@ P.ret u
        val cloop = substVar (loop, z) cz
        val (goalL, holeL) = makeTrue (I @ [(u,P.DIM)], H) (cloop, NONE, K.top)

        (* coherence *)
        val l0 = substSymbol (P.APP P.DIM0, u) holeL
        val l1 = substSymbol (P.APP P.DIM1, u) holeL
        val goalCoh0 = makeEqIfDifferent (I, H) ((l0, holeB), (cbase, NONE, K.top)) (* holeB well-typed *)
        val goalCoh1 = makeEqIfAllDifferent (I, H) ((l1, holeB), (cbase, NONE, K.top)) [l0]

        (* realizer *)
        val elim = Syn.into @@ Syn.S1_REC ((z, cz), VarKit.toExp z, (holeB, (u, holeL)))
      in
        |>: goalB >: goalL >:? goalCoh0 >:? goalCoh1 >: goalKind #> (I, H, elim)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected circle elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.EqElim"
        val (I, H) >> CJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.S1_REC ((x, c0x), m0, (b0, (u, l0u))) = Syn.out elim0
        val Syn.S1_REC ((y, c1y), m1, (b1, (v, l1v))) = Syn.out elim1

        val S1 = Syn.into Syn.S1

        (* motive *)
        val z = alpha 0
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val goalC = makeEqType (I, H @> (z, CJ.TRUE (S1, SOME inherentLevel, inherentKind))) ((c0z, c1z), l, k)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (S1, NONE, K.top))

        (* result type *)
        val goalTy = makeEqTypeIfDifferent (I, H) ((substVar (m0, x) c0x, ty), l, k) (* c0m0 type *)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, x) c0x
        val goalB = makeEq (I, H) ((b0, b1), (cbase, NONE, K.top))

        (* loop branch*)
        val w = alpha 1
        val l0w = substSymbol (P.ret w, u) l0u
        val l1w = substSymbol (P.ret w, v) l1v
        val cloop = substVar (Syn.into @@ Syn.LOOP (P.ret w), x) c0x
        val goalL = makeEq (I @ [(w,P.DIM)], H) ((l0w, l1w), (cloop, NONE, K.top))

        (* coherence *)
        val l00 = substSymbol (P.APP P.DIM0, u) l0u
        val l01 = substSymbol (P.APP P.DIM1, u) l0u
        val goalCoh0 = makeEqIfAllDifferent (I, H) ((l00, b0), (cbase, NONE, K.top)) [b1]
        val goalCoh1 = makeEqIfAllDifferent (I, H) ((l01, b0), (cbase, NONE, K.top)) [l00, b1]
      in
        |>: goalC >: goalM >: goalB >: goalL >:? goalTy >:? goalCoh0 >:? goalCoh1
        #> (I, H, trivial)
      end
  end

  structure DFun =
  struct
    val kindConstraintsOnDomAndCod =
      fn K.DISCRETE => (K.DISCRETE, K.DISCRETE)
       | K.KAN => (K.COE, K.KAN)
       | K.HCOM => (K.CUBICAL, K.HCOM)
       | K.COE => (K.COE, K.COE)
       | K.CUBICAL => (K.CUBICAL, K.CUBICAL)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.EqType"
        val (I, H) >> CJ.EQ_TYPE ((dfun0, dfun1), l, k) = jdg
        val Syn.DFUN (a0, x, b0x) = Syn.out dfun0
        val Syn.DFUN (a1, y, b1y) = Syn.out dfun1
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = makeEqType (I, H) ((a0, a1), l, ka)

        (* codomain *)
        val z = alpha 0
        val b0z = VarKit.rename (z, x) b0x
        val b1z = VarKit.rename (z, y) b1y
        val goalB = makeEqType (I, H @> (z, CJ.TRUE (a0, l, ka))) ((b0z, b1z), l, kb)
      in
        |>: goalA >: goalB #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected dfun typehood sequent"]

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Eq"
        val (I, H) >> CJ.EQ ((lam0, lam1), (dfun, l, k)) = jdg
        val Syn.LAM (x, m0x) = Syn.out lam0
        val Syn.LAM (y, m1y) = Syn.out lam1
        val Syn.DFUN (a, z, bz) = Syn.out dfun
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = makeType (I, H) (a, l, ka)

        (* function *)
        val w = alpha 0
        val m0w = VarKit.rename (w, x) m0x
        val m1w = VarKit.rename (w, y) m1y
        val bw = VarKit.rename (w, z) bz
        val goalM = makeEq (I, H @> (w, CJ.TRUE (a, l, ka))) ((m0w, m1w), (bw, l, kb))
      in
        |>: goalM >: goalA #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.True"
        val (I, H) >> CJ.TRUE (dfun, l, k) = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain*)
        val goalA = makeType (I, H) (a, l, ka)

        (* function *)
        val z = alpha 0
        val bz = VarKit.rename (z, x) bx
        val (goalLam, hole) = makeTrue (I, H @> (z, CJ.TRUE (a, l, ka))) (bz, l, kb)

        (* realizer *)
        val lam = Syn.intoLam (z, hole)
      in
        |>: goalLam >: goalA #> (I, H, lam)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected dfun truth sequent"]

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "DFun.Eta"
        val (I, H) >> CJ.EQ ((m, n), (dfun, l, k)) = jdg
        val Syn.DFUN (_, x, _) = Syn.out dfun

        val m' = Syn.intoLam (x, Syn.intoApp (m, VarKit.toExp x))
        val goal1 = makeMem (I, H) (m, (dfun, l, k))
        val goal2 = makeEqIfDifferent (I, H) ((m', n), (dfun, NONE, K.top))
      in
        |>:? goal2 >: goal1 #> (I, H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Elim"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (dfun, l', _) = Hyps.lookup z H
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        (* argument *)
        val (goalA, holeA) = makeTrue (I, H) (a, NONE, K.top)

        (* new context *)
        val b' = substVar (holeA, x) bx
        val u = alpha 0
        val v = alpha 1
        val aptm = Syn.intoApp (VarKit.toExp z, holeA)
        (* note: a and bx come from the telescope so they are types *)
        val H' = Hyps.interposeAfter
          (z, |@> (u, CJ.TRUE (b', l', K.top))
               @> (v, CJ.EQ ((VarKit.toExp u, aptm), (b', l', K.top))))
          H

        val (goalF, holeF) = makeGoal @@ (I, H') >> catjdg
      in
        |>: goalA >: goalF #> (I, H, VarKit.substMany [(aptm, u), (trivial, v)] holeF)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "DFun.EqApp"
        val (I, H) >> CJ.EQ ((ap0, ap1), (ty, l, k)) = jdg
        val Syn.APP (m0, n0) = Syn.out ap0
        val Syn.APP (m1, n1) = Syn.out ap1

        val (goalDFun, holeDFun) = makeSynth (I, H) (m0, NONE, K.top)
        val (goalDom, holeDom) = makeMatch (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeMatch (O.MONO O.DFUN, 1, holeDFun, [], [n0])
        val goalFunEq = makeEqIfDifferent (I, H) ((m0, m1), (holeDFun, NONE, K.top))
        val goalArgEq = makeEq (I, H) ((n0, n1), (holeDom, NONE, K.top))
        val goalTyEq = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((holeCod, ty), l, k) (NONE, K.top)
      in
        |>: goalDFun >: goalDom >: goalCod >:? goalFunEq >: goalArgEq >:? goalTyEq
        #> (I, H, trivial)
      end
  end

  structure Record =
  struct
    structure Fields = Syn.Fields

    val kindConstraintsOnHeadAndTail =
      fn K.DISCRETE => (K.DISCRETE, K.DISCRETE)
       | K.KAN => (K.KAN, K.KAN)
       | K.HCOM => (K.HCOM, K.KAN)
       | K.COE => (K.COE, K.COE)
       | K.CUBICAL => (K.CUBICAL, K.CUBICAL)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Record.EqType"
        val (I, H) >> CJ.EQ_TYPE ((record0, record1), l, k) = jdg
        val Syn.RECORD fields0 = Syn.out record0
        val Syn.RECORD fields1 = Syn.out record1
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        val fresh = makeNamePopper alpha

        val {goals, ...} =
          ListPair.foldlEq
            (fn (((lbl0, var0), ty0), ((lbl1, var1), ty1), {goals, hyps, ren0, ren1, isFirst}) =>
               let
                 val () = Assert.labelEq "Record.EqType" (lbl0, lbl1)
                 val var = fresh ()
                 val ty0' = renameVars ren0 ty0
                 val ty1' = renameVars ren1 ty1
                 val kind = if isFirst then headKind else tailKind
                 val goals' = goals >: makeEqType (I, hyps) ((ty0', ty1'), l, kind)
                 val hyps' = hyps @> (var, CJ.TRUE (ty0', l, kind))
                 val ren0' = Var.Ctx.insert ren0 var0 var
                 val ren1' = Var.Ctx.insert ren1 var1 var
               in
                 {goals = goals', hyps = hyps', ren0 = ren0', ren1 = ren1', isFirst = false}
               end)
            {goals = T.empty, hyps = H, ren0 = Var.Ctx.empty, ren1 = Var.Ctx.empty, isFirst = true}
            (fields0, fields1)
      in
        goals #> (I, H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "Record.Eq"
        val (I, H) >> CJ.EQ ((tuple0, tuple1), (record, l, k)) = jdg
        val Syn.RECORD fields = Syn.out record
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        (* these operations could be expensive *)
        val Syn.TUPLE map0 = Syn.out tuple0
        val Syn.TUPLE map1 = Syn.out tuple1

        val {goals, famGoals, ...} = 
          List.foldl
            (fn (((lbl, var), ty), {goals, famGoals, env, hyps, isFirst}) =>
               let
                 val ty' = substVarenv env ty
                 val m0 = Fields.lookup lbl map0
                 val m1 = Fields.lookup lbl map1
                 val env' = Var.Ctx.insert env var m0
                 val kind = if isFirst then headKind else tailKind
                 val goals' = goals >: makeEq (I, H) ((m0, m1), (ty', l, kind))
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType (I, hyps) (ty, l, kind)
                 val hyps' = hyps @> (var, CJ.TRUE (ty, l, kind))
               in
                 {goals = goals', famGoals = famGoals', env = env', hyps = hyps', isFirst = false}
               end)
            {goals = T.empty, famGoals = T.empty, env = Var.Ctx.empty, hyps = H, isFirst = true}
            fields
      in
        T.append goals famGoals #> (I, H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "Record.True"
        val (I, H) >> CJ.TRUE (record, l, k) = jdg
        val Syn.RECORD fields = Syn.out record
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        val {goals, famGoals, elements, ...} =
          List.foldl
            (fn (((lbl, var), ty), {goals, famGoals, elements, env, hyps, isFirst}) =>
               let
                 val kind = if isFirst then headKind else tailKind
                 val hyps' = hyps @> (var, CJ.TRUE (ty, l, kind))
                 val ty' = substVarenv env ty
                 val (elemGoal, elemHole) = makeTrue (I, H) (ty', l, kind)
                 val env' = Var.Ctx.insert env var elemHole
                 val goals' = goals >: elemGoal
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType (I, hyps) (ty, l, kind)
                 val elements' = (lbl, ([],[]) \ elemHole) :: elements
               in
                 {goals = goals', famGoals = famGoals', elements = elements', env = env', hyps = hyps', isFirst = false}
               end)
            {goals = T.empty, famGoals = T.empty, elements = [], env = Var.Ctx.empty, hyps = H, isFirst = true}
            fields
        val (lbls, holes) = ListPair.unzip @@ List.rev elements
        val tuple = O.MONO (O.TUPLE lbls) $$ holes
      in
        T.append goals famGoals #> (I, H, tuple)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Record.Eta"
        val (I, H) >> CJ.EQ ((m, n), (record, l, k)) = jdg
        val Syn.RECORD rcd = Syn.out record
        val dom = List.map (#1 o #1) rcd

        fun goLabel lbl = ([],[]) \ (Syn.into @@ Syn.PROJ (lbl, m))

        val m' = O.MONO (O.TUPLE dom) $$ List.map goLabel dom
        val goal1 = makeMem (I, H) (m, (record, l, k))
        val goal2 = makeEqIfDifferent (I, H) ((m', n), (record, l, k)) (* m' well-typed *)
      in
        |>:? goal2 >: goal1 #> (I, H, trivial)
      end

    fun MatchRecord _ jdg =
      let
        val _ = RedPrlLog.trace "Record.MatchRecord"
        val MATCH_RECORD (lbl, tm, tuple) = jdg

        val Abt.$ (O.MONO (O.RECORD lbls), args) = Abt.out tm

        val i = #1 (Option.valOf (ListUtil.findEqIndex lbl lbls))
        val ((_,us) \ ty) = List.nth (args, i)

        (* supply the dependencies *)
        val lblPrefix = List.take (lbls, i)
        val projs = List.map (fn lbl => Syn.into @@ Syn.PROJ (lbl, tuple)) lblPrefix
        val ty = VarKit.substMany (ListPair.zipEq (projs, us)) ty
      in
        Lcf.|> (T.empty, abtToAbs ty)
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH_RECORD judgment failed to unify"]

    fun EqProj _ jdg =
      let
        val _ = RedPrlLog.trace "Record.EqProj"
        val (I, H) >> CJ.EQ ((proj0, proj1), (ty, l, k)) = jdg
        val Syn.PROJ (lbl0, m0) = Syn.out proj0
        val Syn.PROJ (lbl1, m1) = Syn.out proj1
        val () = Assert.labelEq "Record.EqProj" (lbl0, lbl1)

        val (goalTy, holeTy) = makeSynth (I, H) (m0, NONE, K.top)
        val (goalTyP, holeTyP) = makeMatchRecord (lbl0, holeTy, m0)
        val goalEq = makeEqIfDifferent (I, H) ((m0, m1), (holeTy, NONE, K.top)) (* m0 well-typed *)
        val goalEqTy = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((holeTyP, ty), l, k) (NONE, K.top) (* holeTyP type *)
      in
        |>: goalTy >: goalTyP >:? goalEq >:? goalEqTy
        #> (I, H, trivial)
      end

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Record.Elim"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (record, l', _) = Hyps.lookup z H
        val Syn.RECORD fields = Syn.out record

        val names = List.tabulate (List.length fields, alpha)
        val {hyps, ...} =
          ListPair.foldlEq
            (fn (name, ((_, var), ty), {ren, hyps}) =>
              {ren = Var.Ctx.insert ren var name,
               hyps = hyps @> (name, CJ.TRUE (renameVars ren ty, l', K.top))})
            {ren = Var.Ctx.empty, hyps = Hyps.empty}
            (names, fields)
        val tuple = Syn.into @@ Syn.TUPLE @@
          ListPair.mapEq
            (fn (((lbl, _), _), name) => (lbl, Syn.into @@ Syn.VAR (name, O.EXP)))
            (fields, names)
        val H' = Hyps.interposeThenSubstAfter (z, hyps, tuple) H

        val (goal, hole) = makeGoal @@ (I, H') >> CJ.map (substVar (tuple, z)) catjdg

        val projEnv =
          ListPair.foldlEq
            (fn (((lbl, _), _), name, env) =>
              Var.Ctx.insert env name @@ Syn.into @@ Syn.PROJ (lbl, VarKit.toExp z))
            Var.Ctx.empty (fields, names)
      in
        |>: goal #> (I, H, substVarenv projEnv hole)
      end
  end

  structure Path =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.HCOM
       | K.COE => K.KAN
       | K.CUBICAL => K.CUBICAL

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.EqType"
        val (I, H) >> CJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.PATH_TY ((u, a0u), m0, n0) = Syn.out ty0
        val Syn.PATH_TY ((v, a1v), m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val w = alpha 0
        val a0w = substSymbol (P.ret w, u) a0u
        val a1w = substSymbol (P.ret w, v) a1v
        val tyGoal = makeEqType (I @ [(w,P.DIM)], H) ((a0w, a1w), l, ka)

        val a00 = substSymbol (P.APP P.DIM0, u) a0u
        val a01 = substSymbol (P.APP P.DIM1, u) a0u
        val goal0 = makeEq (I, H) ((m0, m1), (a00, NONE, K.top))
        val goal1 = makeEq (I, H) ((n0, n1), (a01, NONE, K.top))
      in
        |>: tyGoal >: goal0 >: goal1 #> (I, H, trivial)
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.Eq"
        val (I, H) >> CJ.EQ ((abs0, abs1), (ty, l, k)) = jdg
        val Syn.PATH_TY ((u, au), p0, p1) = Syn.out ty
        val ka = kindConstraintOnBase k
        val Syn.PATH_ABS (v, m0v) = Syn.out abs0
        val Syn.PATH_ABS (w, m1w) = Syn.out abs1

        val z = alpha 0
        val az = substSymbol (P.ret z, u) au
        val m0z = substSymbol (P.ret z, v) m0v
        val m1z = substSymbol (P.ret z, w) m1w
        val goalM = makeEq (I @ [(z,P.DIM)], H) ((m0z, m1z), (az, l, ka))

        val a0 = substSymbol (P.APP P.DIM0, u) au
        val a1 = substSymbol (P.APP P.DIM1, u) au
        val m00 = substSymbol (P.APP P.DIM0, v) m0v
        val m01 = substSymbol (P.APP P.DIM1, v) m0v
        (* note: m00 and m01 are well-typed and az is well-kinded  *)
        val goalCoh0 = makeEqIfDifferent (I, H) ((m00, p0), (a0, NONE, K.top))
        val goalCoh1 = makeEqIfDifferent (I, H) ((m01, p1), (a1, NONE, K.top))
      in
        |>: goalM >:? goalCoh0 >:? goalCoh1 #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.True"
        val (I, H) >> CJ.TRUE (ty, l, k) = jdg
        val Syn.PATH_TY ((u, au), p0, p1) = Syn.out ty
        val ka = kindConstraintOnBase k
        val a0 = substSymbol (P.APP P.DIM0, u) au
        val a1 = substSymbol (P.APP P.DIM1, u) au

        val v = alpha 0
        val av = substSymbol (P.ret v, u) au
        val (mainGoal, mhole) = makeTrue (I @ [(v,P.DIM)], H) (av, l, ka)

        (* note: m0 and m1 are already well-typed *)
        val m0 = substSymbol (P.APP P.DIM0, v) mhole
        val m1 = substSymbol (P.APP P.DIM1, v) mhole
        val goalCoh0 = makeEqIfDifferent (I, H) ((m0, p0), (a0, NONE, K.top))
        val goalCoh1 = makeEqIfDifferent (I, H) ((m1, p1), (a1, NONE, K.top))

        val abstr = Syn.into @@ Syn.PATH_ABS (v, mhole)
      in
        |>: mainGoal >:? goalCoh0 >:? goalCoh1 #> (I, H, abstr)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Path.Eta"
        val (I, H) >> CJ.EQ ((m, n), (pathTy, l, k)) = jdg
        val Syn.PATH_TY ((u, _), _, _) = Syn.out pathTy

        val m' = Syn.into @@ Syn.PATH_ABS (u, Syn.into @@ Syn.PATH_APP (m, P.ret u))
        val goal1 = makeMem (I, H) (m, (pathTy, l, k))
        val goal2 = makeEqIfDifferent (I, H) ((m', n), (pathTy, NONE, K.top)) (* m' will-typed *)
      in
        |>:? goal2 >: goal1 #> (I, H, trivial)
      end

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Path.Elim"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, l', _) = Hyps.lookup z H
        val Syn.PATH_TY ((u, a), _, _) = Syn.out ty

        val x = alpha 0
        val y = alpha 1
        
        val (dimGoal, dimHole) = makeTerm (I, H) @@ O.PARAM_EXP O.DIM
        val (arGoal, arHole) = makeDimSubst (I, H) (dimHole, u, a)

        val w = Sym.named "w"
        val (pathAppGoal, pathAppHole) = makeDimSubst (I, H) (dimHole, w, Syn.into @@ Syn.PATH_APP (VarKit.toExp z, P.ret w))

        val H' = Hyps.interposeAfter
          (z, |@> (x, CJ.TRUE (arHole, l', K.top))
               @> (y, CJ.EQ ((VarKit.toExp x, pathAppHole), (arHole, l', K.top))))
          H

        val (mainGoal, mainHole) = makeGoal @@ (I, H') >> catjdg
      in
        |>: dimGoal >: arGoal >: pathAppGoal >: mainGoal
        #> (I, H, VarKit.substMany [(pathAppHole, x), (trivial, y)] mainHole)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "Path.EqApp"
        val (I, H) >> CJ.EQ ((ap0, ap1), (ty, l, k)) = jdg
        val Syn.PATH_APP (m0, r0) = Syn.out ap0
        val Syn.PATH_APP (m1, r1) = Syn.out ap1
        val () = Assert.paramEq "Path.EqApp" (r0, r1)

        val (goalSynth, holeSynth) = makeSynth (I, H) (m0, NONE, K.top)
        val goalMem = makeEqIfDifferent (I, H) ((m0, m1), (holeSynth, NONE, K.top)) (* m0 well-typed *)
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holeSynth, [r0], [])
        val goalTy = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((holeLine, ty), l, k) (NONE, K.top) (* holeLine type *)
      in
        |>: goalSynth >:? goalMem >: goalLine >:? goalTy #> (I, H, trivial)
      end

    fun EqAppConst _ jdg =
      let
        val _ = RedPrlLog.trace "Path.EqAppConst"
        val (I, H) >> CJ.EQ ((ap, p), (a, l, k)) = jdg
        val Syn.PATH_APP (m, P.APP r) = Syn.out ap

        val (goalSynth, holeSynth) = makeSynth (I, H) (m, NONE, K.top)

        val dimAddr = case r of P.DIM0 => 1 | P.DIM1 => 2 | _ => E.raiseError (E.INVALID_DIMENSION (TermPrinter.ppParam (P.APP r)))
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holeSynth, [P.APP r], [])
        val (goalEndpoint, holeEndpoint) = makeMatch (O.MONO O.PATH_TY, dimAddr, holeSynth, [], [])
        val goalTy = makeEqTypeIfDifferent (I, H) ((holeLine, a), NONE, K.top) (* holeLine should be well-typed *)
        val goalEq = makeEq (I, H) ((holeEndpoint, p), (a, l, k))
      in
        |>: goalSynth >: goalLine >: goalEndpoint >: goalEq >:? goalTy
        #> (I, H, trivial)
      end
  end

  structure InternalizedEquality =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.DISCRETE
       | K.HCOM => K.CUBICAL
       | K.COE => K.DISCRETE
       | K.CUBICAL => K.CUBICAL

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.EqType"
        val (I, H) >> CJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.EQUALITY (a0, m0, n0) = Syn.out ty0
        val Syn.EQUALITY (a1, m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val goalTy = makeEqType (I, H) ((a0, a1), l, ka)
        val goalM = makeEq (I, H) ((m0, m1), (a0, NONE, K.top))
        val goalN = makeEq (I, H) ((n0, n1), (a0, NONE, K.top))
      in
        |>: goalM >: goalN >: goalTy #> (I, H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Eq"
        val (I, H) >> CJ.EQ ((ax0, ax1), (ty, l, k)) = jdg
        val Syn.EQUALITY (a, m, n) = Syn.out ty
        val ka = kindConstraintOnBase k
        val Syn.AX = Syn.out ax0
        val Syn.AX = Syn.out ax1

        val goal = makeEq (I, H) ((m, n), (a, l, ka))
      in
        |>: goal #> (I, H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.True"
        val (I, H) >> CJ.TRUE (ty, l, k) = jdg
        val Syn.EQUALITY (a, m, n) = Syn.out ty
        val ka = kindConstraintOnBase k

        val goal = makeEq (I, H) ((m, n), (a, l, ka))
      in
        |>: goal #> (I, H, Syn.into Syn.AX)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Eta"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.EQUALITY _ = Syn.out ty

        val goal1 = makeMem (I, H) (m, (ty, l, k))
        val goal2 = makeEqIfDifferent (I, H) ((Syn.into Syn.AX, n), (ty, NONE, K.top))
      in
        |>:? goal2 >: goal1 #> (I, H, trivial)
      end

    (* This rule will be removed once every hypothesis
     * is required to be `A true`. *)
    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Elim"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, l', _) = Hyps.lookup z H
        val Syn.EQUALITY (a, m, n) = Syn.out ty

        (* Adding an equality judgment diverges from Nuprl, but this is currently
         * useful because in RedPRL we do not demand everything in the context to
         * be a true judgment (yet). *)
        val u = alpha 0
        val ax = Syn.into Syn.AX
        val (goal, hole) =
          makeGoal
            @@ (I, Hyps.interposeThenSubstAfter (z, |@> (u, CJ.EQ ((m, n), (a, l', K.top))), ax) H)
            >> CJ.map (substVar (ax, z)) catjdg
      in
        |>: goal #> (I, H, VarKit.subst (trivial, u) hole)
      end
  end

  structure FormalComposition =
  struct
    val kindConstraintOnCapAndTubes =
      fn K.DISCRETE => (K.DISCRETE, K.DISCRETE) (* XXX more research needed *)
       | K.KAN => (K.KAN, K.KAN)
       | K.HCOM => (K.HCOM, K.KAN) (* XXX more research needed *)
       | K.COE => (K.COM, K.KAN) (* XXX more research needed *)
       | K.CUBICAL => (K.CUBICAL, K.COE) (* XXX more research needed *)

    (* see the function of th same name in `ComKit` *)
    local
      fun genTubeGoals' (I, H) ((tubes0, tubes1), l, k) =
        ListPairUtil.mapPartialEq
          (fn ((eq, t0), (_, t1)) => Restriction.makeEqType [eq] (I, H) ((t0, t1), l, k))
          (tubes0, tubes1)
      fun genInterTubeGoalsExceptDiag' (I, H) ((tubes0, tubes1), l, k) =
        ComKit.enumInterExceptDiag
          (fn ((eq0, t0), (eq1, t1)) => Restriction.makeEqTypeIfDifferent [eq0, eq1] (I, H) ((t0, t1), l, k))
          (tubes0, tubes1)
    in
      fun genInterTubeGoals (I, H) w ((tubes0, tubes1), l, k) =
        let
          val tubes0 = ComKit.alphaRenameTubes w tubes0
          val tubes1 = ComKit.alphaRenameTubes w tubes1

          val goalsOnDiag = genTubeGoals' (I @ [(w,P.DIM)], H) ((tubes0, tubes1), l, k)
          val goalsNotOnDiag = genInterTubeGoalsExceptDiag' (I @ [(w,P.DIM)], H) ((tubes0, tubes1), NONE, K.top)
        in
          goalsOnDiag @ goalsNotOnDiag
        end
    end

    (* see the function of th same name in `ComKit` *)
    fun genCapTubeGoalsIfDifferent (I, H) ((cap, (r, tubes)), l, k) =
      List.mapPartial
        (fn (eq, (u, tube)) =>
          Restriction.makeEqTypeIfDifferent [eq] (I, H) ((cap, substSymbol (r, u) tube), l, k))
        tubes

    fun genBoundaryGoals (I, H) ((boundaries0, boundaries1), (tubes, l, k)) =
      ListPairUtil.mapPartialEq
        (fn (((eq, b0), t), (_, b1)) => Restriction.makeEq [eq] (I, H) ((b0, b1), (t, l, k)))
        (ListPair.zipEq (boundaries0, tubes), boundaries1)
    fun genInterBoundaryGoalsExceptDiag (I, H) ((boundaries0, boundaries1), (tubes, l, k)) =
      ComKit.enumInterExceptDiag
        (fn (((eq0, b0), t), (eq1, b1)) => Restriction.makeEqIfDifferent [eq0, eq1] (I, H) ((b0, b1), (t, l, k)))
        (ListPair.zipEq (boundaries0, tubes), boundaries1)
    fun genInterBoundaryGoals (I, H) ((boundaries0, boundaries1), (tubes, l, k)) =
      genBoundaryGoals (I, H) ((boundaries0, boundaries1), (tubes, l, k)) @
      genInterBoundaryGoalsExceptDiag (I, H) ((boundaries0, boundaries1), (tubes, NONE, K.top))

    fun genCapBoundaryGoals (I, H) ((cap, ((r, r'), tyTubes, boundaries)), (tyCap, l, k)) =
      ListPairUtil.mapPartialEq
        (fn ((eq, ty), boundary) =>
          Restriction.makeEqIfDifferent [eq] (I, H)
            ((cap, Syn.into (Syn.COE {dir=(r', r), ty=ty, coercee=boundary})), (tyCap, l, k)))
        (tyTubes, boundaries)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "FormalComposition.EqType"
        val (I, H) >> CJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.FCOM {dir=dir0, cap=cap0, tubes=tubes0} = Syn.out ty0
        val Syn.FCOM {dir=dir1, cap=cap1, tubes=tubes1} = Syn.out ty1
        val () = Assert.dirEq "FormalComposition.EqType direction" (dir0, dir1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = Assert.equationsEq "FormalComposition.EqType equations" (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "FormalComposition.EqType tautology checking" eqs0

        val (kCap, kTube) = kindConstraintOnCapAndTubes k

        val goalCap = makeEqType (I, H) ((cap0, cap1), l, kCap)

        val w = alpha 0
      in
        |>: goalCap
         >:+ genInterTubeGoals (I, H) w ((tubes0, tubes1), l, kTube)
         >:+ genCapTubeGoalsIfDifferent (I, H) ((cap0, (#1 dir0, tubes0)), NONE, K.top)
        #> (I, H, trivial)
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "FormalComposition.Eq"
        val (I, H) >> CJ.EQ ((box0, box1), (ty, l, k)) = jdg
        val Syn.FCOM {dir, cap=tyCap, tubes=tyTubes} = Syn.out ty
        val Syn.BOX {dir=dir0, cap=cap0, boundaries=boundaries0} = Syn.out box0
        val Syn.BOX {dir=dir1, cap=cap1, boundaries=boundaries1} = Syn.out box1
        val () = Assert.dirEq "FormalComposition.Eq direction" (dir0, dir1)
        val () = Assert.dirEq "FormalComposition.Eq direction" (dir0, dir)
        val (eqs0, boundaries') = ListPair.unzip boundaries0
        val eqs1 = List.map #1 boundaries1
        val (eqs, tyTubes') = ListPair.unzip tyTubes
        val _ = Assert.equationsEq "FormalComposition.Eq equations" (eqs0, eqs1)
        val _ = Assert.equationsEq "FormalComposition.Eq equations" (eqs0, eqs)
        val _ = Assert.tautologicalEquations "FormalComposition.Eq tautology checking" eqs

        val (kCap, kTube) = kindConstraintOnCapAndTubes k

        val goalCap = makeEq (I, H) ((cap0, cap1), (tyCap, l, kCap))

        val tyBoundaries = List.map (fn (u, ty) => substSymbol (#2 dir, u) ty) tyTubes'

        val w = alpha 0
      in
        |>: goalCap
         >:+ genInterBoundaryGoals (I, H) ((boundaries0, boundaries1), (tyBoundaries, NONE, K.top))
         >:+ genCapBoundaryGoals (I, H) ((cap0, (dir, tyTubes, boundaries')), (tyCap, NONE, K.top))
         >:+ genInterTubeGoals (I, H) w ((tyTubes, tyTubes), l, kTube)
         >:+ genCapTubeGoalsIfDifferent (I, H) ((tyCap, (#1 dir, tyTubes)), NONE, K.top)
        #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "FormalComposition.True"
        val (I, H) >> CJ.TRUE (ty, l, k) = jdg
        val Syn.FCOM {dir, cap=tyCap, tubes=tyTubes} = Syn.out ty
        val (eqs, tyTubes') = ListPair.unzip tyTubes
        val _ = Assert.tautologicalEquations "FormalComposition.True tautology checking" eqs

        val (kCap, kTube) = kindConstraintOnCapAndTubes k

        val (goalCap, holeCap) = makeTrue (I, H) (tyCap, l, kCap)

        fun goTube (eq, (u, tyTube)) =
          Restriction.makeTrue [eq] (Syn.into Syn.AX) (I, H) (substSymbol (#2 dir, u) tyTube, NONE, K.top)
        val goalHoleBoundaries = List.map goTube tyTubes
        val goalBoundaries = List.mapPartial #1 goalHoleBoundaries
        val holeBoundaries = List.map #2 goalHoleBoundaries

        val tyBoundaries = List.map (fn (u, ty) => substSymbol (#2 dir, u) ty) tyTubes'
        val holeBoundaries' = ListPair.zipEq (eqs, holeBoundaries)

        val w = alpha 0

        val box = Syn.into @@ Syn.BOX {dir=dir, cap=holeCap, boundaries=holeBoundaries'}
      in
        |>: goalCap
         >:+ goalBoundaries
         >:+ genInterBoundaryGoalsExceptDiag (I, H) ((holeBoundaries', holeBoundaries'), (tyBoundaries, NONE, K.top))
         >:+ genCapBoundaryGoals (I, H) ((holeCap, (dir, tyTubes, holeBoundaries)), (tyCap, NONE, K.top))
         >:+ genInterTubeGoals (I, H) w ((tyTubes, tyTubes), l, kTube)
         >:+ genCapTubeGoalsIfDifferent (I, H) ((tyCap, (#1 dir, tyTubes)), NONE, K.top)
        #> (I, H, box)
      end

    (* TODO Add the Elim, EqCap and Eta rules. *)
  end

  structure Univalence =
  struct
    val kindConstraintOnEnds =
      fn K.DISCRETE => E.raiseError (E.UNIMPLEMENTED (Fpp.text "discrete univalence types"))
       | K.KAN => (K.KAN, K.KAN)
       | K.HCOM => (K.HCOM, K.KAN) (* XXX more research needed *)
       | K.COE => (K.COE, K.COM) (* XXX more research needed *)
       | K.CUBICAL => (K.CUBICAL, K.CUBICAL)

    fun intoHasAllPaths C =
      let
        val c = Var.named "c"
        val c' = Var.named "c'"
        val dummy = Sym.named "_"
      in
        Syn.into @@ Syn.DFUN (C, c,
          Syn.into @@ Syn.DFUN (C, c',
            Syn.into @@ Syn.PATH_TY ((dummy, C), VarKit.toExp c, VarKit.toExp c')))
      end

    fun intoIsContr C =
      let
        val center = Var.named "center"
      in
        Syn.intoDProd [(center, C)] @@ intoHasAllPaths C
      end

    fun intoFiber A B f b =
      let
        val a = Var.named "a"
        val dummy = Sym.named "_"
      in
        Syn.intoDProd [(a, A)] @@
          Syn.into @@ Syn.PATH_TY
            ((dummy, B), Syn.intoApp (f, VarKit.toExp a), b)
      end

    fun intoIsEquiv A B f =
      let
        val b = Var.named "b"
      in
        Syn.into @@ Syn.DFUN
          (B, b, intoIsContr (intoFiber A B f (VarKit.toExp b)))
      end

    fun intoEquiv A B =
      let
        val f = Var.named "f"
        val dummy = Var.named "_"
      in
        Syn.intoDProd [(f, Syn.into @@ Syn.DFUN (A, dummy, B))] @@
          intoIsEquiv A B (VarKit.toExp f)
      end

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Univalence.EqType"
        val (I, H) >> CJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.UNIVALENCE (r0, a0, b0, e0) = Syn.out ty0
        val Syn.UNIVALENCE (r1, a1, b1, e1) = Syn.out ty1
        val () = Assert.paramEq "Univalence.EqType" (r0, r1)
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r0, P.APP P.DIM0)

        val goalA = Restriction.makeEqType [eq] (I, H) ((a0, a1), l, kA)
        val goalB = makeEqType (I, H) ((b0, b1), l, kB)
        val goalEquiv = Restriction.makeEq [eq] (I, H)
          ((e0, e1), (intoEquiv a0 b0, NONE, K.top))
      in
        |>:? goalEquiv >:? goalA >: goalB #> (I, H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "Univalence.Eq"
        val (I, H) >> CJ.EQ ((in0, in1), (ty, l, k)) = jdg
        val Syn.UNIVALENCE (r, a, b, e) = Syn.out ty
        val Syn.UNIVALENCE_IN (r0, m0, n0) = Syn.out in0
        val Syn.UNIVALENCE_IN (r1, m1, n1) = Syn.out in1
        val () = Assert.paramEq "Univalence.Eq" (r0, r1)
        val () = Assert.paramEq "Univalence.Eq" (r0, r)
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r0, P.APP P.DIM0)

        val goalM = Restriction.makeEq [eq] (I, H) ((m0, m1), (a, l, kA))
        val goalN = makeEq (I, H) ((n0, n1), (b, l, kB))
        val goalCoh = Restriction.makeEqIfDifferent [eq] (I, H)
          ((Syn.intoApp (Syn.into @@ Syn.PROJ ("f", e), m0), n0), (b, NONE, K.top))
        val goalEquiv = Restriction.makeMem [eq] (I, H) (e, (intoEquiv a b, NONE, K.top))
      in
        |>:? goalM >: goalN >:? goalCoh >:? goalEquiv #> (I, H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "Univalence.True"
        val (I, H) >> CJ.TRUE (ty, l, k) = jdg
        val Syn.UNIVALENCE (r, a, b, e) = Syn.out ty
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r, P.APP P.DIM0)

        val (goalM, holeM) = Restriction.makeTrue [eq] (Syn.into Syn.AX) (I, H) (a, l, kA)
        val (goalN, holeN) = makeTrue (I, H) (b, l, kB)
        val goalCoh = Restriction.makeEqIfDifferent [eq] (I, H)
          ((Syn.intoApp (Syn.into @@ Syn.PROJ ("f", e), holeM), holeN), (b, NONE, K.top))
        val goalEquiv = Restriction.makeMem [eq] (I, H) (e, (intoEquiv a b, NONE, K.top))
      in
        |>:? goalM >: goalN >:? goalCoh >:? goalEquiv
        #> (I, H, Syn.into @@ Syn.UNIVALENCE_IN (r, holeM, holeN))
      end

    (* TODO Add the Elim, EqProj and Eta rules. *)
  end

  structure Universe =
  struct
    val inherentKind =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.COE
       | K.COE => K.COE
       | K.CUBICAL => K.COE

    fun inherentLevel l = SOME (L.above (l, 1))

    (* The following should be equivalent to
     * `L.P.<= (inherentLevel l', l) andalso K.<= (inherentKind k', k)`
     *)
    fun member (l', k') (l, k) = L.P.< (SOME l', l) andalso K.<= (inherentKind k', k)

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.EqType"
        val (I, H) >> CJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty0
        val Syn.UNIVERSE (l1, k1) = Syn.out ty1
        val _ = Assert.levelEq (l0, l1)
        val _ = Assert.kindEq (k0, k1)
        val true = member (l0, k0) (l, k)
      in
        T.empty #> (I, H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.Eq"
        val (I, H) >> CJ.EQ ((a, b), (ty, l, k)) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty
        val true = member (l0, k0) (l, k)

        val goal = makeEqType (I, H) ((a, b), SOME l0, k0)
      in
        |>: goal #> (I, H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.True"
        val (I, H) >> CJ.TRUE (ty, l, k) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty
        val true = member (l0, k0) (l, k)

        val (goalTy, holeTy) = makeTerm (I, H) O.EXP
        val goalTy' = makeType (I, H) (holeTy, SOME l0, k0)
      in
        |>: goalTy >: goalTy' #> (I, H, Syn.into Syn.AX)
      end

    (* This rule will be removed once every hypothesis
     * is required to be `A true`. *)
    fun ElimFromTrue z alpha jdg =
      let
        val _ = RedPrlLog.trace "Universe.ElimFromTrue"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val CJ.TRUE (ty, _, _) = Hyps.lookup z H
        val Syn.UNIVERSE (l, k) = Syn.out ty

        val u = alpha 0
        val (goal, hole) =
          makeGoal
            @@ (I, Hyps.interposeAfter (z, |@> (u, CJ.TYPE (VarKit.toExp z, SOME l, k))) H)
            >> catjdg
      in
        |>: goal #> (I, H, VarKit.subst (trivial, u) hole)
      end

    (* This rule will also be removed once every hypothesis
     * is required to be `A true`. *)
    fun ElimFromEq z alpha jdg =
      let
        val _ = RedPrlLog.trace "Universe.ElimFromEq"
        val (I, H) >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val CJ.EQ ((ty1, ty2), (univ, _, _)) = Hyps.lookup z H
        val Syn.UNIVERSE (l, k) = Syn.out univ

        val u = alpha 0
        val (goal, hole) =
          makeGoal
            @@ (I, Hyps.interposeAfter (z, |@> (u, CJ.EQ_TYPE ((ty1, ty2), SOME l, k))) H)
            >> catjdg
      in
        |>: goal #> (I, H, VarKit.subst (trivial, u) hole)
      end

    fun Elim z = ElimFromTrue z orelse_ ElimFromEq z
  end
end
