(* type-specific modules *)
functor RefinerTypeRules (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  open RedPrlAbt Kit ComRefinerKit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = AJ.jdg
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
   *   For example, we have EqApp for Fun and Path, and EqProj for Record.
   * EqTypeElim/EqTypeX: similar to EqElim but for EQ_TYPE judgments.
   * SynthElim/SynthX: synthesizing the types of eliminators.
   * (others): other special rules for this type.
   *)

  (* Remember to consult `alpha` whenever some goals introduce new hypotheses
   * or new parameter variables.
   *)

  (* Here is the function that will be used in other types *)
  structure Universe =
  struct
    val inherentKind =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.COE
       | K.COE => K.COE
       | K.STABLE => K.COE

    fun inherentLevel l = L.plus (l, 1)
  end

  structure Bool =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqType"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqTT"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.BOOL = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqFF"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.BOOL = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.BOOL = Syn.out ty

        (* tt branch *)
        val tt = Syn.into Syn.TT
        val Htt = Hyps.substAfter (z, tt) H
        val (goalT, holeT) = makeGoal @@ Htt >> AJ.map (substVar (tt, z)) catjdg

        (* ff branch *)
        val ff = Syn.into Syn.FF
        val Hff = Hyps.substAfter (z, ff) H
        val (goalF, holeF) = makeGoal @@ Hff >> AJ.map (substVar (ff, z)) catjdg

        val evidence =
          case catjdg of
             AJ.TRUE _ => Syn.into @@ Syn.IF (VarKit.toExp z, (holeT, holeF))
           | AJ.EQ _ => trivial
           | AJ.EQ_TYPE _ => trivial
           | AJ.SYNTH _ => Syn.into @@ Syn.IF (VarKit.toExp z, (holeT, holeF))
           | _ => raise Fail "Bool.Elim cannot be called with this kind of goal"
      in
        |>: goalT >: goalF #> (H, evidence)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected strict bool elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqElim"
        val H >> AJ.EQ ((if0, if1), (ty, l, k)) = jdg
        val Syn.IF (m0, (t0, f0)) = Syn.out if0
        val Syn.IF (m1, (t1, f1)) = Syn.out if1

        (* motive *)
        val x = alpha 0
        val Hx = H @> (x, AJ.TRUE (Syn.into Syn.BOOL, inherentLevel, inherentKind))
        val (goalTy, holeTy) = makeTerm Hx O.EXP
        val goalTy' = makeType Hx (holeTy, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq H ((m0, m1), (Syn.into Syn.BOOL, NONE, K.top))

        (* result type*)
        val goalTy0 = makeSubType H (substVar (m0, x) holeTy, NONE, K.top) (ty, l, k)

        (* tt branch *)
        val goalT = makeEq H ((t0, t1), (substVar (Syn.into Syn.TT, x) holeTy, NONE, K.top))

        (* ff branch *)
        val goalF = makeEq H ((f0, f1), (substVar (Syn.into Syn.FF, x) holeTy, NONE, K.top))
      in
        |>: goalTy >: goalM >: goalT >: goalF >:? goalTy0 >: goalTy' #> (H, trivial)
      end
  end

  structure WBool =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.KAN

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqType"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.WBOOL = Syn.out a
        val Syn.WBOOL = Syn.out b
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqTT"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqFF"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqFCom"
        val H >> AJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs

        val w = alpha 0
      in
        |>:+ (ComKit.genEqFComGoals H w (args0, args1) (ty, NONE, K.top))
        #> (H, trivial)
      end

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.Elim"
        val H >> AJ.TRUE (cz, l, k) = jdg
        (* if(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.WBOOL = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType H (cz, l, k)

        (* tt branch *)
        val (goalT, holeT) = makeTrue H (substVar (Syn.into Syn.TT, z) cz, NONE, K.top)

        (* ff branch *)
        val (goalF, holeF) = makeTrue H (substVar (Syn.into Syn.FF, z) cz, NONE, K.top)

        (* realizer *)
        val if_ = Syn.into @@ Syn.WIF ((z, cz), VarKit.toExp z, (holeT, holeF))
      in
        |>: goalT >: goalF >: goalKind #> (H, if_)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected bool elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqElim"
        val H >> AJ.EQ ((if0, if1), (ty, l, k)) = jdg
        (* if(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.WIF ((x, c0x), m0, (t0, f0)) = Syn.out if0
        val Syn.WIF ((y, c1y), m1, (t1, f1)) = Syn.out if1

        (* motive *)
        val z = alpha 0
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val Hz = H @> (z, AJ.TRUE (Syn.into Syn.WBOOL, inherentLevel, inherentKind))
        val goalTy = makeEqType Hz ((c0z, c1z), NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq H ((m0, m1), (Syn.into Syn.WBOOL, NONE, K.top))

        (* result type*)
        val goalTy0 = makeSubType H (substVar (m0, x) c0x, NONE, K.top) (ty, l, k)

        (* tt branch *)
        val goalT = makeEq H ((t0, t1), (substVar (Syn.into Syn.TT, x) c0x, NONE, K.top))

        (* ff branch *)
        val goalF = makeEq H ((f0, f1), (substVar (Syn.into Syn.FF, x) c0x, NONE, K.top))
      in
        |>: goalM >: goalT >: goalF >:? goalTy0 >: goalTy #> (H, trivial)
      end

    fun SynthElim _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.SynthElim"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.WIF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem H (tm, (cm, l, k))
      in
        |>: goal #> (H, cm)
      end
  end

  structure Nat =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqType"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.NAT = Syn.out a
        val Syn.NAT = Syn.out b
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqZero"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.NAT = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun EqSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqSucc"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.NAT = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq H ((m', n'), (Syn.into Syn.NAT, NONE, K.top))
      in
        |>: goal #> (H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.Elim"
        val H >> AJ.TRUE (cz, l, k) = jdg
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.NAT = Syn.out ty

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* zero branch *)
        val (goalZ, holeZ) = makeTrue H (substVar (zero, z) cz, l, k)

        (* succ branch *)
        val u = alpha 0
        val v = alpha 1
        val cu = VarKit.rename (u, z) cz
        val (goalS, holeS) =
          makeTrue
            (H @> (u, AJ.TRUE (nat, inherentLevel, inherentKind)) @> (v, AJ.TRUE (cu, l, k)))
            (substVar (succ @@ VarKit.toExp u, z) cz, l, k)

        (* realizer *)
        val evidence = Syn.into @@ Syn.NAT_REC (VarKit.toExp z, (holeZ, (u, v, holeS)))
      in
        |>: goalZ >: goalS #> (H, evidence)
      end

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqElim"
        val H >> AJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        val Syn.NAT_REC (m0, (n0, (a0, b0, p0))) = Syn.out elim0
        val Syn.NAT_REC (m1, (n1, (a1, b1, p1))) = Syn.out elim1

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* motive *)
        val z = alpha 0
        val Hz = H @> (z, AJ.TRUE (nat, inherentLevel, inherentKind))
        val (goalC, holeC) = makeTerm Hz O.EXP
        val goalC' = makeType Hz (holeC, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq H ((m0, m1), (nat, NONE, K.top))

        (* result type *)
        val goalTy = makeSubType H (substVar (m0, z) holeC, NONE, K.top) (ty, l, k)

        (* zero branch *)
        val goalZ = makeEq H ((n0, n1), (substVar (zero, z) holeC, NONE, K.top))

        (* succ branch *)
        val u = alpha 1
        val v = alpha 2
        val cu = VarKit.rename (u, z) holeC
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            (H @> (u, AJ.TRUE (nat, inherentLevel, inherentKind)) @> (v, AJ.TRUE (cu, l, k)))
            ((p0, p1), (substVar (succ @@ VarKit.toExp u, z) holeC, NONE, K.top))
      in
        |>: goalC >: goalM >: goalZ >: goalS >: goalC' >:? goalTy #> (H, trivial)
      end

    fun EqTypeElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqTypeElim"
        val H >> AJ.EQ_TYPE ((elim0, elim1), l, k) = jdg
        val Syn.NAT_REC (m0, (n0, (a0, b0, p0))) = Syn.out elim0
        val Syn.NAT_REC (m1, (n1, (a1, b1, p1))) = Syn.out elim1

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* motive *)
        val z = alpha 0
        val Hz = H @> (z, AJ.TRUE (nat, inherentLevel, inherentKind))
        val (goalC, holeC) = makeTerm Hz O.EXP
        val goalC' = makeType Hz (holeC, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq H ((m0, m1), (nat, NONE, K.top))

        (* result type *)
        val goalTy = makeSubUniverse H (substVar (m0, z) holeC, l, k)

        (* zero branch *)
        val goalZ = makeEq H ((n0, n1), (substVar (zero, z) holeC, NONE, K.top))

        (* succ branch *)
        val u = alpha 1
        val v = alpha 2
        val cu = VarKit.rename (u, z) holeC
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            (H @> (u, AJ.TRUE (nat, inherentLevel, inherentKind))
                  @> (v, AJ.TRUE (cu, Universe.inherentLevel l, Universe.inherentKind k)))
            ((p0, p1), (substVar (succ @@ VarKit.toExp u, z) holeC, NONE, K.top))
      in
        |>: goalC >: goalM >: goalZ >: goalS >: goalC' >: goalTy #> (H, trivial)
      end
  end

  structure Int =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqType"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.INT = Syn.out a
        val Syn.INT = Syn.out b
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqZero"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun EqSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqSucc"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq H ((m', n'), (Syn.into Syn.NAT, NONE, K.top))
      in
        |>: goal #> (H, trivial)
      end

    fun EqNegSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqNegSucc"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.NEGSUCC m' = Syn.out m
        val Syn.NEGSUCC n' = Syn.out n
        val goal = makeEq H ((m', n'), (Syn.into Syn.NAT, NONE, K.top))
      in
        |>: goal #> (H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Int.Elim"
        val H >> AJ.TRUE (cz, l, k) = jdg
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.INT = Syn.out ty

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC
        val negsucc = Syn.into o Syn.NEGSUCC

        (* zero branch *)
        val (goalZ, holeZ) = makeTrue H (substVar (zero, z) cz, l, k)

        (* succ branch *)
        val u = alpha 0
        val v = alpha 1
        val cu = VarKit.rename (u, z) cz
        val (goalS, holeS) =
          makeTrue
            (H @> (u, AJ.TRUE (nat, Nat.inherentLevel, Nat.inherentKind)) @> (v, AJ.TRUE (cu, l, k)))
            (substVar (succ @@ VarKit.toExp u, z) cz, l, k)

        (* (negsucc zero) branch *)
        val (goalNSZ, holeNSZ) = makeTrue H (substVar (negsucc zero, z) cz, l, k)

        (* (negsucc succ) branch *)
        val cnegsuccu = Abt.substVar (negsucc @@ VarKit.toExp u, z) cz
        val (goalNSS, holeNSS) =
          makeTrue
            (H @> (u, AJ.TRUE (nat, Nat.inherentLevel, Nat.inherentKind)) @> (v, AJ.TRUE (cnegsuccu, l, k)))
            (substVar (negsucc @@ succ @@ VarKit.toExp u, z) cz, l, k)

        (* realizer *)
        val evidence = Syn.into @@ Syn.INT_REC (VarKit.toExp z, (holeZ, (u, v, holeS), holeNSZ, (u, v, holeNSS)))
      in
        |>: goalZ >: goalS >: goalNSZ >: goalNSS #> (H, evidence)
      end

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Int.EqElim"
        val H >> AJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        val Syn.INT_REC (m0, (n0, (a0, b0, p0), q0, (c0, d0, r0))) = Syn.out elim0
        val Syn.INT_REC (m1, (n1, (a1, b1, p1), q1, (c1, d1, r1))) = Syn.out elim1

        val int = Syn.into Syn.INT
        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC
        val negsucc = Syn.into o Syn.NEGSUCC

        (* motive *)
        val z = alpha 0
        val Hz = H @> (z, AJ.TRUE (int, inherentLevel, inherentKind))
        val (goalC, holeC) = makeTerm Hz O.EXP
        val goalC' = makeType Hz (holeC, NONE, K.top)

        (* eliminated term *)
        val goalM = makeEq H ((m0, m1), (int, NONE, K.top))

        (* result type *)
        val goalTy = makeSubType H (substVar (m0, z) holeC, NONE, K.top) (ty, l, k)

        (* zero branch *)
        val goalZ = makeEq H ((n0, n1), (substVar (zero, z) holeC, NONE, K.top))

        (* succ branch *)
        val u = alpha 1
        val v = alpha 2
        val cu = VarKit.rename (u, z) holeC
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            (H @> (u, AJ.TRUE (nat, Nat.inherentLevel, Nat.inherentKind)) @> (v, AJ.TRUE (cu, l, k)))
            ((p0, p1), (substVar (succ @@ VarKit.toExp u, z) holeC, NONE, K.top))

        (* (negsucc zero) branch *)
        val goalNSZ = makeEq H ((q0, q1), (substVar (negsucc zero, z) holeC, NONE, K.top))

        (* (negsucc succ) branch *)
        val cnegsuccu = Abt.substVar (negsucc @@ VarKit.toExp u, z) holeC
        val r0 = VarKit.renameMany [(u, c0), (v, d0)] r0
        val r1 = VarKit.renameMany [(u, c1), (v, d1)] r1
        val goalNSS =
          makeEq
            (H @> (u, AJ.TRUE (nat, l, Nat.inherentKind)) @> (v, AJ.TRUE (cnegsuccu, l, k)))
            ((r0, r1), (substVar (negsucc @@ succ @@ VarKit.toExp u, z) holeC, NONE, K.top))
      in
        |>: goalC >: goalM >: goalZ >: goalS >: goalNSZ >: goalNSS >: goalC' >:? goalTy #> (H, trivial)
      end
  end

  structure Void =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Void.EqType"
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.VOID = Syn.out a
        val Syn.VOID = Syn.out b
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Void.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.VOID = Syn.out ty

        val evidence =
          case catjdg of
             AJ.TRUE _ => Syn.into Syn.AX (* should be some fancy variable *)
           | AJ.EQ _ => trivial
           | AJ.EQ_TYPE _ => trivial
           | AJ.SYNTH _ => Syn.into Syn.AX
           | _ => raise Fail "Void.Elim cannot be called with this kind of goal"
      in
        T.empty #> (H, evidence)
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
        val H >> AJ.EQ_TYPE ((a, b), l, k) = jdg
        val Syn.S1 = Syn.out a
        val Syn.S1 = Syn.out b
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqBase _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqBase"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.BASE = Syn.out m
        val Syn.BASE = Syn.out n
      in
        T.empty #> (H, trivial)
      end

    fun EqLoop _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqLoop"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.LOOP r1 = Syn.out m
        val Syn.LOOP r2 = Syn.out n
        val () = Assert.alphaEq' "S1.EqLoop" (r1, r2)
      in
        T.empty #> (H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.EqFCom"
        val H >> AJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs

        val w = alpha 0
      in
        |>:+ (ComKit.genEqFComGoals H w (args0, args1) (ty, NONE, K.top))
        #> (H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.Elim"
        val H >> AJ.TRUE (cz, l, k) = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.S1 = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType H (cz, l, k)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, z) cz
        val (goalB, holeB) = makeTrue H (cbase, NONE, K.top)

        (* loop branch *)
        val u = alpha 0
        val loop = Syn.into o Syn.LOOP @@ VarKit.toDim u
        val cloop = substVar (loop, z) cz
        val (goalL, holeL) = makeTrue (H @> (u, AJ.TERM O.DIM)) (cloop, NONE, K.top)

        (* coherence *)
        val l0 = substVar (Syn.into Syn.DIM0, u) holeL
        val l1 = substVar (Syn.into Syn.DIM1, u) holeL
        val goalCoh0 = makeEqIfDifferent H ((l0, holeB), (cbase, NONE, K.top)) (* holeB well-typed *)
        val goalCoh1 = makeEqIfAllDifferent H ((l1, holeB), (cbase, NONE, K.top)) [l0]

        (* realizer *)
        val elim = Syn.into @@ Syn.S1_REC ((z, cz), VarKit.toExp z, (holeB, (u, holeL)))
      in
        |>: goalB >: goalL >:? goalCoh0 >:? goalCoh1 >: goalKind #> (H, elim)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected circle elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.EqElim"
        val H >> AJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.S1_REC ((x, c0x), m0, (b0, (u, l0u))) = Syn.out elim0
        val Syn.S1_REC ((y, c1y), m1, (b1, (v, l1v))) = Syn.out elim1

        val S1 = Syn.into Syn.S1

        (* motive *)
        val z = alpha 0
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val goalC = makeEqType (H @> (z, AJ.TRUE (S1, inherentLevel, inherentKind))) ((c0z, c1z), l, k)

        (* eliminated term *)
        val goalM = makeEq H ((m0, m1), (S1, NONE, K.top))

        (* result type *)
        val goalTy = makeSubType H (substVar (m0, x) c0x, l, k) (ty, l, k) (* c0m0 type *)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, x) c0x
        val goalB = makeEq H ((b0, b1), (cbase, NONE, K.top))

        (* loop branch*)
        val w = alpha 1
        val l0w = substVar (VarKit.toDim w, u) l0u
        val l1w = substVar (VarKit.toDim w, v) l1v
        val cloop = substVar (Syn.into @@ Syn.LOOP (VarKit.toDim w), x) c0x
        val goalL = makeEq (H @> (w, AJ.TERM O.DIM)) ((l0w, l1w), (cloop, NONE, K.top))

        (* coherence *)
        val l00 = substVar (Syn.into Syn.DIM0, u) l0u
        val l01 = substVar (Syn.into Syn.DIM1, u) l0u
        val goalCoh0 = makeEqIfAllDifferent H ((l00, b0), (cbase, NONE, K.top)) [b1]
        val goalCoh1 = makeEqIfAllDifferent H ((l01, b0), (cbase, NONE, K.top)) [l00, b1]
      in
        |>: goalC >: goalM >: goalB >: goalL >:? goalTy >:? goalCoh0 >:? goalCoh1
        #> (H, trivial)
      end

    fun SynthElim _ jdg =
      let
        val _ = RedPrlLog.trace "S1.SynthElim"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.S1_REC ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem H (tm, (cm, l, k))
      in
        |>: goal #> (H, cm)
      end
  end

  structure Fun =
  struct
    val kindConstraintsOnDomAndCod =
      fn K.DISCRETE => (K.DISCRETE, K.DISCRETE)
       | K.KAN => (K.COE, K.KAN)
       | K.HCOM => (K.STABLE, K.HCOM)
       | K.COE => (K.COE, K.COE)
       | K.STABLE => (K.STABLE, K.STABLE)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Fun.EqType"
        val H >> AJ.EQ_TYPE ((fun0, fun1), l, k) = jdg
        val Syn.FUN (a0, x, b0x) = Syn.out fun0
        val Syn.FUN (a1, y, b1y) = Syn.out fun1
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = makeEqType H ((a0, a1), l, ka)

        (* codomain *)
        val z = alpha 0
        val b0z = VarKit.rename (z, x) b0x
        val b1z = VarKit.rename (z, y) b1y
        val goalB = makeEqType (H @> (z, AJ.TRUE (a0, l, ka))) ((b0z, b1z), l, kb)
      in
        |>: goalA >: goalB #> (H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected fun typehood sequent"]

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Fun.Eq"
        val H >> AJ.EQ ((lam0, lam1), (ty, l, k)) = jdg
        val Syn.LAM (x, m0x) = Syn.out lam0
        val Syn.LAM (y, m1y) = Syn.out lam1
        val Syn.FUN (a, z, bz) = Syn.out ty
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = makeType H (a, l, ka)

        (* function *)
        val w = alpha 0
        val m0w = VarKit.rename (w, x) m0x
        val m1w = VarKit.rename (w, y) m1y
        val bw = VarKit.rename (w, z) bz
        val goalM = makeEq (H @> (w, AJ.TRUE (a, l, ka))) ((m0w, m1w), (bw, l, kb))
      in
        |>: goalM >: goalA #> (H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Fun.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.FUN (a, x, bx) = Syn.out ty
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain*)
        val goalA = makeType H (a, l, ka)

        (* function *)
        val z = alpha 0
        val bz = VarKit.rename (z, x) bx
        val (goalLam, hole) = makeTrue (H @> (z, AJ.TRUE (a, l, ka))) (bz, l, kb)

        (* realizer *)
        val lam = Syn.intoLam (z, hole)
      in
        |>: goalLam >: goalA #> (H, lam)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected fun truth sequent"]

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Fun.Eta"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.FUN (_, x, _) = Syn.out ty

        val m' = Syn.intoLam (x, Syn.intoApp (m, VarKit.toExp x))
        val goal1 = makeMem H (m, (ty, l, k))
        val goal2 = makeEqIfDifferent H ((m', n), (ty, NONE, K.top))
      in
        |>:? goal2 >: goal1 #> (H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Fun.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val AJ.TRUE (ty, l', _) = Hyps.lookup H z
        val Syn.FUN (a, x, bx) = Syn.out ty

        (* argument *)
        val (goalA, holeA) = makeTrue H (a, NONE, K.top)

        (* new context *)
        val b' = substVar (holeA, x) bx
        val u = alpha 0
        val v = alpha 1
        val aptm = Syn.intoApp (VarKit.toExp z, holeA)
        (* note: a and bx come from the telescope so they are types *)
        val H' = Hyps.interposeAfter
          (z, |@> (u, AJ.TRUE (b', l', K.top))
               @> (v, AJ.EQ ((VarKit.toExp u, aptm), (b', l', K.top))))
          H

        val (goalF, holeF) = makeGoal @@ H' >> catjdg
      in
        |>: goalA >: goalF #> (H, VarKit.substMany [(aptm, u), (trivial, v)] holeF)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "Fun.EqApp"
        val H >> AJ.EQ ((ap0, ap1), (ty, l, k)) = jdg
        val Syn.APP (m0, n0) = Syn.out ap0
        val Syn.APP (m1, n1) = Syn.out ap1

        val (goalFun, holeFun) = makeSynth H (m0, NONE, K.top)
        val (goalDom, holeDom) = makeMatch (O.FUN, 0, holeFun, [])
        val (goalCod, holeCod) = makeMatch (O.FUN, 1, holeFun, [n0])
        val goalFunEq = makeEqIfDifferent H ((m0, m1), (holeFun, NONE, K.top))
        val goalArgEq = makeEq H ((n0, n1), (holeDom, NONE, K.top))
        val goalTy = makeSubType H (holeCod, NONE, K.top) (ty, l, k)
      in
        |>: goalFun >: goalDom >: goalCod >:? goalFunEq >: goalArgEq >:? goalTy
        #> (H, trivial)
      end

    fun EqTypeApp _ jdg =
      let
        val _ = RedPrlLog.trace "Fun.EqTypeApp"
        val H >> AJ.EQ_TYPE ((ap0, ap1), l, k) = jdg
        val Syn.APP (m0, n0) = Syn.out ap0
        val Syn.APP (m1, n1) = Syn.out ap1

        val (goalFun, holeFun) = makeSynth H (m0, NONE, K.top)
        val (goalDom, holeDom) = makeMatch (O.FUN, 0, holeFun, [])
        val (goalCod, holeCod) = makeMatch (O.FUN, 1, holeFun, [n0])
        val goalFunEq = makeEqIfDifferent H ((m0, m1), (holeFun, NONE, K.top))
        val goalArgEq = makeEq H ((n0, n1), (holeDom, NONE, K.top))
        val goalTy = makeSubUniverse H (holeCod, l, k)
      in
        |>: goalFun >: goalDom >: goalCod >:? goalFunEq >: goalArgEq >: goalTy
        #> (H, trivial)
      end

    fun SynthApp _ jdg =
      let
        val _ = RedPrlLog.trace "Fun.SynthApp"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.APP (m, n) = Syn.out tm
        val (goalFun, holeFun) = makeSynth H (m, NONE, K.top)
        val (goalDom, holeDom) = makeMatch (O.FUN, 0, holeFun, [])
        val (goalCod, holeCod) = makeMatch (O.FUN, 1, holeFun, [n])
        val goalN = makeMem H (n, (holeDom, NONE, K.top))
        val goalKind = makeTypeUnlessSubUniv H (holeCod, l, k) (NONE, K.top)
      in
        |>: goalFun >: goalDom >: goalCod >: goalN >:? goalKind #> (H, holeCod)
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
       | K.STABLE => (K.STABLE, K.STABLE)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Record.EqType"
        val H >> AJ.EQ_TYPE ((record0, record1), l, k) = jdg
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
                 val goals' = goals >: makeEqType hyps ((ty0', ty1'), l, kind)
                 val hyps' = hyps @> (var, AJ.TRUE (ty0', l, kind))
                 val ren0' = Var.Ctx.insert ren0 var0 var
                 val ren1' = Var.Ctx.insert ren1 var1 var
               in
                 {goals = goals', hyps = hyps', ren0 = ren0', ren1 = ren1', isFirst = false}
               end)
            {goals = T.empty, hyps = H, ren0 = Var.Ctx.empty, ren1 = Var.Ctx.empty, isFirst = true}
            (fields0, fields1)
      in
        goals #> (H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "Record.Eq"
        val H >> AJ.EQ ((tuple0, tuple1), (record, l, k)) = jdg
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
                 val goals' = goals >: makeEq H ((m0, m1), (ty', l, kind))
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType hyps (ty, l, kind)
                 val hyps' = hyps @> (var, AJ.TRUE (ty, l, kind))
               in
                 {goals = goals', famGoals = famGoals', env = env', hyps = hyps', isFirst = false}
               end)
            {goals = T.empty, famGoals = T.empty, env = Var.Ctx.empty, hyps = H, isFirst = true}
            fields
      in
        T.append goals famGoals #> (H, trivial)
      end

    fun EqInv z alpha jdg =
      let
        val H >> ajdg = jdg
        val _ = RedPrlLog.trace "Record.EqInv"
        val AJ.EQ ((m1, m2), (record, l, k)) = Hyps.lookup H z
        val Syn.RECORD fields = Syn.out record
        val fresh = makeNamePopper alpha

        val (hyps, _) =
          List.foldl
            (fn (field, (hyps, env)) =>
               let
                 val ((name, var), ty) = field
                 val proj1 = Syn.into @@ Syn.PROJ (name, m1)
                 val proj2 = Syn.into @@ Syn.PROJ (name, m2)
                 val x = fresh ()
                 val eqjdg = AJ.EQ ((proj1, proj2), (substVarenv env ty, l, k))
                 val env' = Var.Ctx.insert env var proj1
               in
                 (hyps @> (x, eqjdg), env')
               end)
            (Hyps.empty, Var.Ctx.empty)
            fields

        val H' = Hyps.remove z (Hyps.interposeThenSubstAfter (z, hyps, Syn.into Syn.TV) H)
        val ajdg' = AJ.map (substVar (Syn.into Syn.TV, z)) ajdg
        val (goal, hole) = makeGoal @@ H' >> ajdg'
        val extractEnv = Hyps.foldl (fn (x, _, rho) => Var.Ctx.insert rho x (Syn.into Syn.TV)) Var.Ctx.empty hyps
      in
        |>: goal #> (H, substVarenv extractEnv hole)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "Record.True"
        val H >> AJ.TRUE (record, l, k) = jdg
        val Syn.RECORD fields = Syn.out record
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        val {goals, famGoals, elements, ...} =
          List.foldl
            (fn (((lbl, var), ty), {goals, famGoals, elements, env, hyps, isFirst}) =>
               let
                 val kind = if isFirst then headKind else tailKind
                 val hyps' = hyps @> (var, AJ.TRUE (ty, l, kind))
                 val ty' = substVarenv env ty
                 val (elemGoal, elemHole) = makeTrue H (ty', l, kind)
                 val env' = Var.Ctx.insert env var elemHole
                 val goals' = goals >: elemGoal
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType hyps (ty, l, kind)
                 val elements' = (lbl, [] \ elemHole) :: elements
               in
                 {goals = goals', famGoals = famGoals', elements = elements', env = env', hyps = hyps', isFirst = false}
               end)
            {goals = T.empty, famGoals = T.empty, elements = [], env = Var.Ctx.empty, hyps = H, isFirst = true}
            fields
        val (lbls, holes) = ListPair.unzip @@ List.rev elements
        val tuple = O.TUPLE lbls $$ holes
      in
        T.append goals famGoals #> (H, tuple)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Record.Eta"
        val H >> AJ.EQ ((m, n), (record, l, k)) = jdg
        val Syn.RECORD rcd = Syn.out record
        val dom = List.map (#1 o #1) rcd

        fun goLabel lbl = [] \ (Syn.into @@ Syn.PROJ (lbl, m))

        val m' = O.TUPLE dom $$ List.map goLabel dom
        val goal1 = makeMem H (m, (record, l, k))
        val goal2 = makeEqIfDifferent H ((m', n), (record, l, k)) (* m' well-typed *)
      in
        |>:? goal2 >: goal1 #> (H, trivial)
      end

    fun MatchRecord _ jdg =
      let
        val _ = RedPrlLog.trace "Record.MatchRecord"
        val MATCH_RECORD (lbl, tm, tuple) = jdg

        val Abt.$ (O.RECORD lbls, args) = Abt.out tm

        val i = #1 (Option.valOf (ListUtil.findEqIndex lbl lbls))
        val (us \ ty) = List.nth (args, i)

        (* supply the dependencies *)
        val lblPrefix = List.take (lbls, i)
        val projs = List.map (fn lbl => Syn.into @@ Syn.PROJ (lbl, tuple)) lblPrefix
        val ty = VarKit.substMany (ListPair.zipEq (projs, us)) ty
      in
        Lcf.|> (T.empty, abtToAbs ty)
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH_RECORD judgment failed to unify"]

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Record.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val AJ.TRUE (record, l', _) = Hyps.lookup H z
        val Syn.RECORD fields = Syn.out record

        val names = List.tabulate (List.length fields, alpha)
        val {hyps, ...} =
          ListPair.foldlEq
            (fn (name, ((_, var), ty), {ren, hyps}) =>
              {ren = Var.Ctx.insert ren var name,
               hyps = hyps @> (name, AJ.TRUE (renameVars ren ty, l', K.top))})
            {ren = Var.Ctx.empty, hyps = Hyps.empty}
            (names, fields)

        val tuple = Syn.into @@ Syn.TUPLE @@
          ListPair.mapEq
            (fn (((lbl, _), _), name) => (lbl, Syn.into @@ Syn.VAR (name, O.EXP)))
            (fields, names)

        val H' = Hyps.interposeThenSubstAfter (z, hyps, tuple) H

        val (goal, hole) = makeGoal @@ H' >> AJ.map (substVar (tuple, z)) catjdg

        val projEnv =
          ListPair.foldlEq
            (fn (((lbl, _), _), name, env) =>
              Var.Ctx.insert env name @@ Syn.into @@ Syn.PROJ (lbl, VarKit.toExp z))
            Var.Ctx.empty (fields, names)
      in
        |>: goal #> (H, substVarenv projEnv hole)
      end
      handle _ => raise E.error [Fpp.text "Record.Elim"]

    fun EqProj _ jdg =
      let
        val _ = RedPrlLog.trace "Record.EqProj"
        val H >> AJ.EQ ((proj0, proj1), (ty, l, k)) = jdg
        val Syn.PROJ (lbl0, m0) = Syn.out proj0
        val Syn.PROJ (lbl1, m1) = Syn.out proj1
        val () = Assert.labelEq "Record.EqProj" (lbl0, lbl1)

        val (goalTy, holeTy) = makeSynth H (m0, NONE, K.top)
        val (goalTyP, holeTyP) = makeMatchRecord (lbl0, holeTy, m0)
        val goalEq = makeEqIfDifferent H ((m0, m1), (holeTy, NONE, K.top)) (* m0 well-typed *)
        val goalTy' = makeSubType H (holeTyP, NONE, K.top) (ty, l, k)
      in
        |>: goalTy >: goalTyP >:? goalEq >:? goalTy'
        #> (H, trivial)
      end

    fun SynthProj _ jdg =
      let
        val _ = RedPrlLog.trace "Record.SynthProj"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.PROJ (lbl, n) = Syn.out tm
        val (goalRecord, holeRecord) = makeSynth H (n, NONE, K.top)
        val (goalTy, holeTy) = makeMatchRecord (lbl, holeRecord, n)
        val goalKind = makeTypeUnlessSubUniv H (holeTy, l, k) (NONE, K.top)
      in
        |>: goalRecord >: goalTy >:? goalKind #> (H, holeTy)
      end
  end

  structure Path =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.HCOM
       | K.COE => K.KAN
       | K.STABLE => K.STABLE

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.PATH ((u, a0u), m0, n0) = Syn.out ty0
        val Syn.PATH ((v, a1v), m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val w = alpha 0
        val a0w = substVar (VarKit.toDim w, u) a0u
        val a1w = substVar (VarKit.toDim w, v) a1v
        val tyGoal = makeEqType (H @> (w, AJ.TERM O.DIM)) ((a0w, a1w), l, ka)

        val a00 = substVar (Syn.into Syn.DIM0, u) a0u
        val a01 = substVar (Syn.into Syn.DIM1, u) a0u
        val goal0 = makeEq H ((m0, m1), (a00, NONE, K.top))
        val goal1 = makeEq H ((n0, n1), (a01, NONE, K.top))
      in
        |>: tyGoal >: goal0 >: goal1 #> (H, trivial)
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.Eq"
        val H >> AJ.EQ ((abs0, abs1), (ty, l, k)) = jdg
        val Syn.PATH ((u, au), p0, p1) = Syn.out ty
        val ka = kindConstraintOnBase k
        val Syn.ABS (v, m0v) = Syn.out abs0
        val Syn.ABS (w, m1w) = Syn.out abs1

        val z = alpha 0
        val az = substVar (VarKit.toDim z, u) au
        val m0z = substVar (VarKit.toDim z, v) m0v
        val m1z = substVar (VarKit.toDim z, w) m1w
        val goalM = makeEq (H @> (z, AJ.TERM O.DIM)) ((m0z, m1z), (az, l, ka))

        val a0 = substVar (Syn.into Syn.DIM0, u) au
        val a1 = substVar (Syn.into Syn.DIM1, u) au
        val m00 = substVar (Syn.into Syn.DIM0, v) m0v
        val m01 = substVar (Syn.into Syn.DIM1, v) m0v
        (* note: m00 and m01 are well-typed and az is well-kinded  *)
        val goalCoh0 = makeEqIfDifferent H ((m00, p0), (a0, NONE, K.top))
        val goalCoh1 = makeEqIfDifferent H ((m01, p1), (a1, NONE, K.top))
      in
        |>: goalM >:? goalCoh0 >:? goalCoh1 #> (H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.PATH ((u, au), p0, p1) = Syn.out ty
        val ka = kindConstraintOnBase k
        val a0 = substVar (Syn.into Syn.DIM0, u) au
        val a1 = substVar (Syn.into Syn.DIM1, u) au

        val v = alpha 0
        val av = substVar (VarKit.toDim v, u) au
        val (mainGoal, mhole) = makeTrue (H @> (v, AJ.TERM O.DIM)) (av, l, ka)

        (* note: m0 and m1 are already well-typed *)
        val m0 = substVar (Syn.into Syn.DIM0, v) mhole
        val m1 = substVar (Syn.into Syn.DIM1, v) mhole
        val goalCoh0 = makeEqIfDifferent H ((m0, p0), (a0, NONE, K.top))
        val goalCoh1 = makeEqIfDifferent H ((m1, p1), (a1, NONE, K.top))

        val abstr = Syn.into @@ Syn.ABS (v, mhole)
      in
        |>: mainGoal >:? goalCoh0 >:? goalCoh1 #> (H, abstr)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Path.Eta"
        val H >> AJ.EQ ((m, n), (pathTy, l, k)) = jdg
        val Syn.PATH ((u, _), _, _) = Syn.out pathTy

        val m' = Syn.into @@ Syn.ABS (u, Syn.into @@ Syn.DIM_APP (m, VarKit.toDim u))
        val goal1 = makeMem H (m, (pathTy, l, k))
        val goal2 = makeEqIfDifferent H ((m', n), (pathTy, NONE, K.top)) (* m' will-typed *)
      in
        |>:? goal2 >: goal1 #> (H, trivial)
      end

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Path.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val AJ.TRUE (ty, l', _) = Hyps.lookup H z
        val Syn.PATH ((u, a), _, _) = Syn.out ty

        val x = alpha 0
        val y = alpha 1
        
        val (dimGoal, dimHole) = makeTerm H @@ O.DIM
        val ar = substVar (dimHole, u) a


        val w = Sym.named "w"
        val pathApp = substVar (dimHole, w) @@ Syn.into @@ Syn.DIM_APP (VarKit.toExp z, VarKit.toDim w)

        val H' = Hyps.interposeAfter
          (z, |@> (x, AJ.TRUE (ar, l', K.top))
               @> (y, AJ.EQ ((VarKit.toExp x, pathApp), (ar, l', K.top))))
          H

        val (mainGoal, mainHole) = makeGoal @@ H' >> catjdg
      in
        |>: dimGoal >: mainGoal
        #> (H, VarKit.substMany [(pathApp, x), (trivial, y)] mainHole)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "Path.EqApp"
        val H >> AJ.EQ ((ap0, ap1), (ty, l, k)) = jdg
        val Syn.DIM_APP (m0, r0) = Syn.out ap0
        val Syn.DIM_APP (m1, r1) = Syn.out ap1
        val () = Assert.alphaEq (r0, r1)

        val (goalSynth, holeSynth) = makeSynth H (m0, NONE, K.top)
        val goalMem = makeEqIfDifferent H ((m0, m1), (holeSynth, NONE, K.top)) (* m0 well-typed *)
        val (goalLine, holeLine) = makeMatch (O.PATH, 0, holeSynth, [r0])
        val goalTy = makeSubType H (holeLine, NONE, K.top) (ty, l, k) (* holeLine type *)
      in
        |>: goalSynth >:? goalMem >: goalLine >:? goalTy #> (H, trivial)
      end

    fun SynthApp _ jdg =
      let
        val _ = RedPrlLog.trace "Path.SynthApp"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.DIM_APP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeSynth H (m, NONE, K.top)
        val (goalLine, holeLine) = makeMatch (O.PATH, 0, holePathTy, [r])
        val goalKind = makeTypeUnlessSubUniv H (holeLine, l, k) (NONE, K.top)
      in
        |>: goalPathTy >: goalLine >:? goalKind #> (H, holeLine)
      end

    fun EqAppConst _ jdg =
      let
        val _ = RedPrlLog.trace "Path.EqAppConst"
        val H >> AJ.EQ ((ap, p), (a, l, k)) = jdg
        val Syn.DIM_APP (m, r) = Syn.out ap

        val dimAddr = case Syn.out r of Syn.DIM0 => 1 | Syn.DIM1 => 2

        val (goalSynth, holeSynth) = makeSynth H (m, NONE, K.top)

        val (goalLine, holeLine) = makeMatch (O.PATH, 0, holeSynth, [r])
        val (goalEndpoint, holeEndpoint) = makeMatch (O.PATH, dimAddr, holeSynth, [])
        val goalTy = makeSubType H (holeLine, NONE, K.top) (a, NONE, K.top) (* holeLine should be well-typed *)
        val goalEq = makeEq H ((holeEndpoint, p), (a, l, k))
      in
        |>: goalSynth >: goalLine >: goalEndpoint >: goalEq >:? goalTy
        #> (H, trivial)
      end
  end

  structure Line =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.HCOM
       | K.COE => K.COE
       | K.STABLE => K.STABLE

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Line.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.LINE (u, a0u) = Syn.out ty0
        val Syn.LINE (v, a1v) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val w = alpha 0
        val a0w = substVar (VarKit.toDim w, u) a0u
        val a1w = substVar (VarKit.toDim w, v) a1v
        val tyGoal = makeEqType (H @> (w, AJ.TERM O.DIM)) ((a0w, a1w), l, ka)
      in
        |>: tyGoal #> (H, trivial)
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Line.Eq"
        val H >> AJ.EQ ((abs0, abs1), (ty, l, k)) = jdg
        val Syn.LINE (u, au) = Syn.out ty
        val ka = kindConstraintOnBase k
        val Syn.ABS (v, m0v) = Syn.out abs0
        val Syn.ABS (w, m1w) = Syn.out abs1

        val z = alpha 0
        val az = substVar (VarKit.toDim z, u) au
        val m0z = substVar (VarKit.toDim z, v) m0v
        val m1z = substVar (VarKit.toDim z, w) m1w
        val goalM = makeEq (H @> (z, AJ.TERM O.DIM)) ((m0z, m1z), (az, l, ka))
      in
        |>: goalM #> (H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Line.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.LINE (u, au) = Syn.out ty
        val ka = kindConstraintOnBase k
        val a0 = substVar (Syn.into Syn.DIM0, u) au
        val a1 = substVar (Syn.into Syn.DIM1, u) au

        val v = alpha 0
        val av = substVar (VarKit.toDim v, u) au
        val (mainGoal, mhole) = makeTrue (H @> (v, AJ.TERM O.DIM)) (av, l, ka)

        val abstr = Syn.into @@ Syn.ABS (v, mhole)
      in
        |>: mainGoal #> (H, abstr)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Line.Eta"
        val H >> AJ.EQ ((m, n), (pathTy, l, k)) = jdg
        val Syn.LINE (u, _) = Syn.out pathTy

        val m' = Syn.into @@ Syn.ABS (u, Syn.into @@ Syn.DIM_APP (m, VarKit.toDim u))
        val goal1 = makeMem H (m, (pathTy, l, k))
        val goal2 = makeEqIfDifferent H ((m', n), (pathTy, NONE, K.top)) (* m' will-typed *)
      in
        |>:? goal2 >: goal1 #> (H, trivial)
      end

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Line.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val AJ.TRUE (ty, l', _) = Hyps.lookup H z
        val Syn.LINE (u, a) = Syn.out ty

        val x = alpha 0
        val y = alpha 1
        
        val (dimGoal, dimHole) = makeTerm H @@ O.DIM
        val ar = substVar (dimHole, u) a

        val w = Sym.named "w"
        val pathApp = substVar (dimHole, w) @@ Syn.into @@ Syn.DIM_APP (VarKit.toExp z, VarKit.toDim w)

        val H' = Hyps.interposeAfter
          (z, |@> (x, AJ.TRUE (ar, l', K.top))
               @> (y, AJ.EQ ((VarKit.toExp x, pathApp), (ar, l', K.top))))
          H

        val (mainGoal, mainHole) = makeGoal @@ H' >> catjdg
      in
        |>: dimGoal >: mainGoal
        #> (H, VarKit.substMany [(pathApp, x), (trivial, y)] mainHole)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "Line.EqApp"
        val H >> AJ.EQ ((ap0, ap1), (ty, l, k)) = jdg
        val Syn.DIM_APP (m0, r0) = Syn.out ap0
        val Syn.DIM_APP (m1, r1) = Syn.out ap1
        val () = Assert.alphaEq (r0, r1)

        val (goalSynth, holeSynth) = makeSynth H (m0, NONE, K.top)
        val goalMem = makeEqIfDifferent H ((m0, m1), (holeSynth, NONE, K.top)) (* m0 well-typed *)
        val (goalLine, holeLine) = makeMatch (O.LINE, 0, holeSynth, [r0])
        val goalTy = makeSubType H (holeLine, NONE, K.top) (ty, l, k) (* holeLine type *)
      in
        |>: goalSynth >:? goalMem >: goalLine >:? goalTy #> (H, trivial)
      end

    fun SynthApp _ jdg =
      let
        val _ = RedPrlLog.trace "Line.SynthApp"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.DIM_APP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeSynth H (m, NONE, K.top)
        val (goalLine, holeLine) = makeMatch (O.LINE, 0, holePathTy, [r])
        val goalKind = makeTypeUnlessSubUniv H (holeLine, l, k) (NONE, K.top)
      in
        |>: goalPathTy >: goalLine >:? goalKind #> (H, holeLine)
      end
  end

  structure Pushout =
  struct
    val kindConstraintOnEndsAndApex =
      fn K.DISCRETE => E.raiseError @@
           E.NOT_APPLICABLE (Fpp.text "Pushouts", Fpp.text "discrete universes")
       | K.KAN => (K.COE, K.COE)
       | K.COE => (K.COE, K.COE)
       | K.HCOM => (K.STABLE, K.STABLE)
       | K.STABLE => (K.STABLE, K.STABLE)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.PUSHOUT (a0, b0, c0, (x0, f0x0), (y0, g0y0)) = Syn.out ty0
        val Syn.PUSHOUT (a1, b1, c1, (x1, f1x1), (y1, g1y1)) = Syn.out ty1

        val (kEnd, kApex) = kindConstraintOnEndsAndApex k
        val goalA = makeEqType H ((a0, a1), l, kEnd)
        val goalB = makeEqType H ((b0, b1), l, kEnd)
        val goalC = makeEqType H ((c0, c1), l, kApex)

        val z = alpha 0
        val f0z = VarKit.rename (z, x0) f0x0
        val f1z = VarKit.rename (z, x1) f1x1
        val goalF = makeEq (H @> (z, AJ.TRUE (c0, l, kApex))) ((f0z, f1z), (a0, L.top, K.top))
        val g0z = VarKit.rename (z, y0) g0y0
        val g1z = VarKit.rename (z, y1) g1y1
        val goalG = makeEq (H @> (z, AJ.TRUE (c0, l, kApex))) ((g0z, g1z), (b0, L.top, K.top))
      in
        |>: goalF >: goalG >: goalA >: goalB >: goalC #> (H, trivial)
      end

    fun EqLeft alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.EqLeft"
        val H >> AJ.EQ ((tm0, tm1), (ty, l, k)) = jdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.LEFT m0 = Syn.out tm0
        val Syn.LEFT m1 = Syn.out tm1
        val (kEnd, kApex) = kindConstraintOnEndsAndApex k

        val goalA = makeEq H ((m0, m1), (a, l, kEnd))

        val goalB = makeType H (b, l, kEnd)
        val goalC = makeType H (c, l, kApex)
        val z = alpha 0
        val goalF = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, x) fx, (a, L.top, K.top))
        val goalG = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, y) gy, (b, L.top, K.top))
      in
        |>: goalA >: goalF >: goalG >: goalB >: goalC #> (H, trivial)
      end

    fun EqRight alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.EqRight"
        val H >> AJ.EQ ((tm0, tm1), (ty, l, k)) = jdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.RIGHT m0 = Syn.out tm0
        val Syn.RIGHT m1 = Syn.out tm1
        val (kEnd, kApex) = kindConstraintOnEndsAndApex k

        val goalB = makeEq H ((m0, m1), (b, l, kEnd))

        val goalA = makeType H (a, l, kEnd)
        val goalC = makeType H (c, l, kApex)
        val z = alpha 0
        val goalF = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, x) fx, (a, L.top, K.top))
        val goalG = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, y) gy, (b, L.top, K.top))
      in
        |>: goalB >: goalF >: goalG >: goalA >: goalC #> (H, trivial)
      end

    fun EqGlue alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.EqGlue"
        val H >> AJ.EQ ((tm0, tm1), (ty, l, k)) = jdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.GLUE (r0, m0, fm0, gm0) = Syn.out tm0
        val Syn.GLUE (r1, m1, fm1, gm1) = Syn.out tm1
        val () = Assert.alphaEq' "Pushout.EqGlue" (r0, r1)
        val (kEnd, kApex) = kindConstraintOnEndsAndApex k

        val goalC = makeEq H ((m0, m1), (c, l, kApex))
        val goalA = makeEq H ((fm0, fm1), (a, l, kEnd))
        val goalB = makeEq H ((gm0, gm1), (b, l, kEnd))
        val z = alpha 0
        val goalF = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, x) fx, (a, L.top, K.top))
        val goalG = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, y) gy, (b, L.top, K.top))

        val goalCohF = makeEq H ((substVar (m0, x) fx, fm0), (a, L.top, K.top))
        val goalCohG = makeEq H ((substVar (m0, y) gy, gm0), (b, L.top, K.top))
      in
        |>: goalC >: goalA >: goalB >: goalCohF >: goalCohG >: goalF >: goalG #> (H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.EqFCom"
        val H >> AJ.EQ ((tm0, tm1), (ty, l, k)) = jdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.FCOM args0 = Syn.out tm0
        val Syn.FCOM args1 = Syn.out tm1

        val (kEnd, kApex) = kindConstraintOnEndsAndApex k
        val goalA = makeType H (a, l, kEnd)
        val goalB = makeType H (b, l, kEnd)
        val goalC = makeType H (c, l, kApex)

        val z = alpha 0
        val goalF = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, x) fx, (a, L.top, K.top))
        val goalG = makeMem (H @> (z, AJ.TRUE (c, l, kApex))) (VarKit.rename (z, y) gy, (b, L.top, K.top))
      in
        |>: goalF >: goalG >: goalA >: goalB >: goalC
         >:+ ComKit.genEqFComGoals H z (args0, args1) (ty, L.top, K.top)
        #> (H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.Elim"
        val H >> AJ.TRUE (dz, l, k) = jdg
        (* pushout-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.PUSHOUT (tyA, tyB, tyC, (x, fx), (y, gy)) = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType H (dz, l, k)

        (* left branch *)
        val a = alpha 0
        val atm = VarKit.toExp a
        fun dleft tm = substVar (Syn.into (Syn.LEFT tm), z) dz
        val (goalL, holeL) = makeTrue (H @> (a, AJ.TRUE (tyA, L.top, K.top))) (dleft atm, L.top, K.top)

        (* right branch *)
        val b = alpha 1
        val btm = VarKit.toExp b
        fun dright tm = substVar (Syn.into (Syn.RIGHT tm), z) dz
        val (goalR, holeR) = makeTrue (H @> (b, AJ.TRUE (tyB, L.top, K.top))) (dright btm, L.top, K.top)

        (* glue branch *)
        val v = alpha 2
        val vtm = VarKit.toDim v
        val c = alpha 3
        val ctm = VarKit.toExp c
        val fc = substVar (ctm, x) fx
        val gc = substVar (ctm, y) gy
        val glue = Syn.into @@ Syn.GLUE (vtm, ctm, fc, gc)
        val dglue = substVar (glue, z) dz
        val Hglue = H @> (v, AJ.TERM O.DIM) @> (c, AJ.TRUE (tyC, L.top, K.top))
        val (goalG, holeG) = makeTrue Hglue (dglue, L.top, K.top)

        (* coherence *)
        val g0c = substVar (Syn.intoDim 0, v) holeG
        val lfc = substVar (fc, a) holeL
        val goalCohL = makeEq (H @> (c, AJ.TRUE (tyC, L.top, K.top))) ((g0c, lfc), (dleft fc, L.top, K.top))

        val g1c = substVar (Syn.intoDim 1, v) holeG
        val rgc = substVar (gc, b) holeR
        val goalCohR = makeEq (H @> (c, AJ.TRUE (tyC, L.top, K.top))) ((g1c, rgc), (dright gc, L.top, K.top))

        val elim = Syn.into @@ Syn.PUSHOUT_REC ((z, dz), VarKit.toExp z, ((a, holeL), (b, holeR), (v, c, holeG)))
      in
        |>: goalL >: goalR >: goalG >: goalCohL >: goalCohR >: goalKind #> (H, elim)
      end

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Pushout.EqElim"
        val H >> AJ.EQ ((elim0, elim1), (ty, l, k)) = jdg
        (* pushout-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.PUSHOUT_REC ((z0, d0z0), m0, ((a0, n0a0), (b0, p0b0), (v0, c0, q0v0c0))) = Syn.out elim0
        val Syn.PUSHOUT_REC ((z1, d1z1), m1, ((a1, n1a1), (b1, p1b1), (v1, c1, q1v1c1))) = Syn.out elim1

        (* type of eliminated term *)
        val (goalTyPushout, holeTyPushout) = makeSynth H (m0, L.top, K.top)

        (* motive *)
        val z = alpha 0
        val d0z = VarKit.rename (z, z0) d0z0
        val d1z = VarKit.rename (z, z1) d1z1
        val goalC = makeEqType (H @> (z, AJ.TRUE (holeTyPushout, L.top, K.top))) ((d0z, d1z), l, k)

        (* eliminated term *)
        val goalM = makeEqIfDifferent H ((m0, m1), (holeTyPushout, L.top, K.top))

        (* result type*)
        val goalTy0 = makeSubType H (substVar (m0, z0) d0z0, L.top, K.top) (ty, l, k)

        (* left branch *)
        val (goalTyA, holeTyA) = makeMatch (O.PUSHOUT, 0, holeTyPushout, [])
        val a = alpha 1
        val atm = VarKit.toExp a
        val n0a = VarKit.rename (a, a0) n0a0
        val n1a = VarKit.rename (a, a1) n1a1
        fun dleft tm = substVar (Syn.into (Syn.LEFT tm), z0) d0z0
        val goalN = makeEq (H @> (a, AJ.TRUE (holeTyA, L.top, K.top))) ((n0a, n1a), (dleft atm, L.top, K.top))

        (* right branch *)
        val (goalTyB, holeTyB) = makeMatch (O.PUSHOUT, 1, holeTyPushout, [])
        val b = alpha 2
        val btm = VarKit.toExp b
        val p0b = VarKit.rename (b, b0) p0b0
        val p1b = VarKit.rename (b, b1) p1b1
        fun dright tm = substVar (Syn.into (Syn.RIGHT tm), z0) d0z0
        val goalP = makeEq (H @> (b, AJ.TRUE (holeTyB, L.top, K.top))) ((p0b, p1b), (dright btm, L.top, K.top))

        (* glue branch *)
        val (goalTyC, holeTyC) = makeMatch (O.PUSHOUT, 2, holeTyPushout, [])
        val v = alpha 2
        val vtm = VarKit.toDim v
        val c = alpha 3
        val ctm = VarKit.toExp c
        val q0vc = VarKit.renameMany [(v, v0), (c, c0)] q0v0c0
        val q1vc = VarKit.renameMany [(v, v1), (c, c1)] q1v1c1
        val (goalF, holeF) = makeMatch (O.PUSHOUT, 3, holeTyPushout, [ctm])
        val (goalG, holeG) = makeMatch (O.PUSHOUT, 4, holeTyPushout, [ctm])
        val glue = Syn.into @@ Syn.GLUE (vtm, ctm, holeF, holeG)
        val dglue = substVar (glue, z0) d0z0
        val Hglue = H @> (v, AJ.TERM O.DIM) @> (c, AJ.TRUE (holeTyC, L.top, K.top))
        val goalQ = makeEq Hglue ((q0vc, q1vc), (dglue, L.top, K.top))

        (* coherence *)
        val q00c = substVar (Syn.intoDim 0, v) q0vc
        val lfc = substVar (holeF, a0) n0a0
        val goalCohL = makeEq (H @> (c, AJ.TRUE (holeTyC, L.top, K.top))) ((q00c, lfc), (dleft holeF, L.top, K.top))

        val q01c = substVar (Syn.intoDim 1, v) q0vc
        val rgc = substVar (holeG, b0) p0b0
        val goalCohR = makeEq (H @> (c, AJ.TRUE (holeTyC, L.top, K.top))) ((q01c, rgc), (dright holeG, L.top, K.top))
      in
        |>: goalTyPushout >: goalC >:? goalM >: goalTyA >: goalN >: goalTyB >: goalP >: goalTyC >: goalF >: goalG >: goalQ >: goalCohL >: goalCohR >:? goalTy0 #> (H, trivial)
      end

    fun SynthElim _ jdg =
      let
        val _ = RedPrlLog.trace "Pushout.SynthElim"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val Syn.PUSHOUT_REC ((z,dz), m, _) = Syn.out tm

        val dm = substVar (m, z) dz
        val goal = makeMem H (tm, (dm, l, k))
      in
        |>: goal #> (H, dm)
      end
  end

  structure InternalizedEquality =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.DISCRETE
       | K.HCOM => K.STABLE
       | K.COE => K.DISCRETE
       | K.STABLE => K.STABLE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.EQUALITY (a0, m0, n0) = Syn.out ty0
        val Syn.EQUALITY (a1, m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val goalTy = makeEqType H ((a0, a1), l, ka)
        val goalM = makeEq H ((m0, m1), (a0, NONE, K.top))
        val goalN = makeEq H ((n0, n1), (a0, NONE, K.top))
      in
        |>: goalM >: goalN >: goalTy #> (H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Eq"
        val H >> AJ.EQ ((ax0, ax1), (ty, l, k)) = jdg
        val Syn.EQUALITY (a, m, n) = Syn.out ty
        val ka = kindConstraintOnBase k
        val Syn.AX = Syn.out ax0
        val Syn.AX = Syn.out ax1

        val goal = makeEq H ((m, n), (a, l, ka))
      in
        |>: goal #> (H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.EQUALITY (a, m, n) = Syn.out ty
        val ka = kindConstraintOnBase k

        val goal = makeEq H ((m, n), (a, l, ka))
      in
        |>: goal #> (H, Syn.into Syn.AX)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Eta"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg
        val Syn.EQUALITY _ = Syn.out ty

        val goal1 = makeMem H (m, (ty, l, k))
        val goal2 = makeEqIfDifferent H ((Syn.into Syn.AX, n), (ty, NONE, K.top))
      in
        |>:? goal2 >: goal1 #> (H, trivial)
      end

    (* This rule will be changed once every hypothesis
     * is required to be `A true`. *)
    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Elim"
        val H >> catjdg = jdg
        (* for now we ignore the kind in the context *)
        val AJ.TRUE (ty, l', _) = Hyps.lookup H z
        val Syn.EQUALITY (a, m, n) = Syn.out ty

        (* Adding an equality judgment diverges from Nuprl, but this is currently
         * useful because in RedPRL we do not demand everything in the context to
         * be a true judgment (yet). *)
        val u = alpha 0
        val ax = Syn.into Syn.AX
        val (goal, hole) =
          makeGoal
            @@ (Hyps.interposeThenSubstAfter (z, |@> (u, AJ.EQ ((m, n), (a, l', K.top))), ax) H)
            >> AJ.map (substVar (ax, z)) catjdg
      in
        |>: goal #> (H, VarKit.subst (trivial, u) hole)
      end

    (* (= ty m n) at l >> m = n in ty at l *)
    (* this is for non-deterministic search *)
    fun NondetEqFromTrueEq z _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.NondetEqFromTrueEq"
        val H >> AJ.EQ ((m1, n1), (ty1, l1, k1)) = jdg
        val AJ.TRUE (ty0', l', _) = Hyps.lookup H z
        val Syn.EQUALITY (ty0, m0, n0) = Syn.out ty0'
        val _ = Assert.alphaEqEither ((m0, n0), m1)
        val _ = Assert.alphaEqEither ((m0, n0), n1)
        val _ = Assert.alphaEq (ty0, ty1)
        val goalTy = makeTypeUnlessSubUniv H (ty1, l1, k1) (l', K.top)
      in
        |>:? goalTy #> (H, trivial)
      end

    (* (= ty m n) at l >> ty = ty at l *)
    (* this is for non-deterministic search *)
    fun NondetTypeFromTrueEqAtType z _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.NondetTypeFromTrueEqAtType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val AJ.TRUE (eq, l', _) = Hyps.lookup H z
        val Syn.EQUALITY (ty', _, _) = Syn.out eq
        val _ = Assert.alphaEq (ty0, ty1)
        val _ = Assert.alphaEq (ty', ty0)
        val _ = Assert.inUsefulUniv (l', K.top) (l, k)
        val goal = makeTypeUnlessSubUniv H (ty0, l, k) (l', K.top)
      in
        |>:? goal #> (H, trivial)
      end

    fun InternalizeEq _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.InternalizeEq"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg

        (* the realizer must be `AX` *)
        val (goal, _) = makeTrue H (Syn.into (Syn.EQUALITY (ty, m, n)), l, K.top)
        val goalKind = makeTypeUnlessSubUniv H (ty, l, k) (l, K.top)
      in
        |>: goal >:? goalKind #> (H, trivial)
      end

    (* (= ty a b) => a synth ~~> ty *)
    fun NondetSynthFromTrueEq z _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.NondetSynthFromTrueEq"
        val H >> AJ.SYNTH (tm, l, k) = jdg
        val AJ.TRUE (equal, l', _) = Hyps.lookup H z
        val Syn.EQUALITY (ty, a, b) = Syn.out equal
        val _ = Assert.alphaEqEither ((a, b), tm)
        val goalKind = makeTypeUnlessSubUniv H (ty, l, k) (l', K.top)
      in
        |>:? goalKind #> (H, ty)
      end

    fun RewriteTrue sel eqterm alpha jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.RewriteTrue"
        val H >> catjdg = jdg

        val (currentTy, l, k) =
          case Selector.lookup sel (H, catjdg) of
             AJ.TRUE params => params
           | jdg => E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "rewrite tactic", AJ.pretty jdg)

        val truncatedH = Selector.truncateFrom sel H

        val (goalTyOfEq, holeTyOfEq) = makeSynth truncatedH (eqterm, NONE, K.top)
        val (goalTy, holeTy) = makeMatch (O.EQUALITY, 0, holeTyOfEq, [])
        val (goalM, holeM) = makeMatch (O.EQUALITY, 1, holeTyOfEq, [])
        val (goalN, holeN) = makeMatch (O.EQUALITY, 2, holeTyOfEq, [])

        val x = alpha 0
        val truncatedHx = truncatedH @> (x, AJ.TRUE (holeTy, NONE, K.top))
        val (motiveGoal, motiveHole) = makeTerm truncatedHx O.EXP
        val motiveWfGoal = makeType truncatedHx (motiveHole, l, k)

        val motiven = substVar (holeN, x) motiveHole
        val motivem = substVar (holeM, x) motiveHole

        fun replace jdg = 
          case jdg of 
             AJ.TRUE (_, l, k) => AJ.TRUE (motiven, l, k)
           | _ => jdg

        val (H', catjdg') = Selector.map sel replace (H, catjdg)
        val (rewrittenGoal, rewrittenHole) = makeGoal @@ H' >> catjdg'

        val motiveMatchesMainGoal =
          case sel of
            O.IN_CONCL => makeSubType truncatedH (motivem, l, k) (currentTy, l, k)
          | O.IN_HYP _ => makeSubType truncatedH (currentTy, l, k) (motivem, l, k)
      in
        |>: goalTyOfEq >: goalTy >: goalM >: goalN
         >: motiveGoal >: rewrittenGoal >: motiveWfGoal >:? motiveMatchesMainGoal
         #> (H, rewrittenHole)
      end

    (* XXX deprecated *)
    fun RewriteTrueByTrue sel z alpha jdg =
      E.raiseError @@ E.GENERIC [Fpp.text "Use rewrite instead."]

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "InternalizedEquality.Symmetry"
        val H >> AJ.TRUE (equal, l, k) = jdg
        val Syn.EQUALITY (ty, m, n) = Syn.out equal
        val (goal, hole) = makeTrue H (Syn.into (Syn.EQUALITY (ty, n, m)), l, k)
      in
        |>: goal #> (H, Syn.into Syn.AX)
      end
  end

  structure FormalComposition =
  struct
    val kindConstraintOnCapAndTubes =
      fn K.DISCRETE => (K.DISCRETE, K.DISCRETE) (* XXX more research needed *)
       | K.KAN => (K.KAN, K.KAN)
       | K.HCOM => (K.HCOM, K.KAN) (* XXX more research needed *)
       | K.COE => (K.COM, K.KAN) (* XXX more research needed *)
       | K.STABLE => (K.STABLE, K.COE) (* XXX more research needed *)

    (* see the function of th same name in `ComKit` *)
    local
      fun genTubeGoals' H ((tubes0, tubes1), l, k) =
        ListPairUtil.mapPartialEq
          (fn ((eq, t0), (_, t1)) => Restriction.makeEqType [eq] H ((t0, t1), l, k))
          (tubes0, tubes1)
      fun genInterTubeGoalsExceptDiag' H ((tubes0, tubes1), l, k) =
        ComKit.enumInterExceptDiag
          (fn ((eq0, t0), (eq1, t1)) => Restriction.makeEqTypeIfDifferent [eq0, eq1] H ((t0, t1), l, k))
          (tubes0, tubes1)
    in
      fun genInterTubeGoals H w ((tubes0, tubes1), l, k) =
        let
          val tubes0 = ComKit.alphaRenameTubes w tubes0
          val tubes1 = ComKit.alphaRenameTubes w tubes1

          val goalsOnDiag = genTubeGoals' (H @> (w, AJ.TERM O.DIM)) ((tubes0, tubes1), l, k)
          val goalsNotOnDiag = genInterTubeGoalsExceptDiag' (H @> (w, AJ.TERM O.DIM)) ((tubes0, tubes1), NONE, K.top)
        in
          goalsOnDiag @ goalsNotOnDiag
        end
    end

    (* see the function of th same name in `ComKit` *)
    fun genCapTubeGoalsIfDifferent H ((cap, (r, tubes)), l, k) =
      List.mapPartial
        (fn (eq, (u, tube)) =>
          Restriction.makeEqTypeIfDifferent [eq] H ((cap, substVar (r, u) tube), l, k))
        tubes

    fun genBoundaryGoals H ((boundaries0, boundaries1), (tubes, l, k)) =
      ListPairUtil.mapPartialEq
        (fn (((eq, b0), t), (_, b1)) => Restriction.makeEq [eq] H ((b0, b1), (t, l, k)))
        (ListPair.zipEq (boundaries0, tubes), boundaries1)
    fun genInterBoundaryGoalsExceptDiag H ((boundaries0, boundaries1), (tubes, l, k)) =
      ComKit.enumInterExceptDiag
        (fn (((eq0, b0), t), (eq1, b1)) => Restriction.makeEqIfDifferent [eq0, eq1] H ((b0, b1), (t, l, k)))
        (ListPair.zipEq (boundaries0, tubes), boundaries1)
    fun genInterBoundaryGoals H ((boundaries0, boundaries1), (tubes, l, k)) =
      genBoundaryGoals H ((boundaries0, boundaries1), (tubes, l, k)) @
      genInterBoundaryGoalsExceptDiag H ((boundaries0, boundaries1), (tubes, NONE, K.top))

    fun genCapBoundaryGoals H ((cap, ((r, r'), tyTubes, boundaries)), (tyCap, l, k)) =
      ListPairUtil.mapPartialEq
        (fn ((eq, ty), boundary) =>
          Restriction.makeEqIfDifferent [eq] H
            ((cap, Syn.into (Syn.COE {dir=(r', r), ty=ty, coercee=boundary})), (tyCap, l, k)))
        (tyTubes, boundaries)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "FormalComposition.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.FCOM {dir=dir0, cap=cap0, tubes=tubes0} = Syn.out ty0
        val Syn.FCOM {dir=dir1, cap=cap1, tubes=tubes1} = Syn.out ty1
        val () = Assert.dirEq "FormalComposition.EqType direction" (dir0, dir1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = Assert.equationsEq "FormalComposition.EqType equations" (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "FormalComposition.EqType tautology checking" eqs0

        val (kCap, kTube) = kindConstraintOnCapAndTubes k

        val goalCap = makeEqType H ((cap0, cap1), l, kCap)

        val w = alpha 0
      in
        |>: goalCap
         >:+ genInterTubeGoals H w ((tubes0, tubes1), l, kTube)
         >:+ genCapTubeGoalsIfDifferent H ((cap0, (#1 dir0, tubes0)), NONE, K.top)
        #> (H, trivial)
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "FormalComposition.Eq"
        val H >> AJ.EQ ((box0, box1), (ty, l, k)) = jdg
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

        val goalCap = makeEq H ((cap0, cap1), (tyCap, l, kCap))

        val tyBoundaries = List.map (fn (u, ty) => substVar (#2 dir, u) ty) tyTubes'

        val w = alpha 0
      in
        |>: goalCap
         >:+ genInterBoundaryGoals H ((boundaries0, boundaries1), (tyBoundaries, NONE, K.top))
         >:+ genCapBoundaryGoals H ((cap0, (dir, tyTubes, boundaries')), (tyCap, NONE, K.top))
         >:+ genInterTubeGoals H w ((tyTubes, tyTubes), l, kTube)
         >:+ genCapTubeGoalsIfDifferent H ((tyCap, (#1 dir, tyTubes)), NONE, K.top)
        #> (H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "FormalComposition.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.FCOM {dir, cap=tyCap, tubes=tyTubes} = Syn.out ty
        val (eqs, tyTubes') = ListPair.unzip tyTubes
        val _ = Assert.tautologicalEquations "FormalComposition.True tautology checking" eqs

        val (kCap, kTube) = kindConstraintOnCapAndTubes k

        val (goalCap, holeCap) = makeTrue H (tyCap, l, kCap)

        fun goTube (eq, (u, tyTube)) =
          Restriction.makeTrue [eq] (Syn.into Syn.AX) H (substVar (#2 dir, u) tyTube, NONE, K.top)
        val goalHoleBoundaries = List.map goTube tyTubes
        val goalBoundaries = List.mapPartial #1 goalHoleBoundaries
        val holeBoundaries = List.map #2 goalHoleBoundaries

        val tyBoundaries = List.map (fn (u, ty) => substVar (#2 dir, u) ty) tyTubes'
        val holeBoundaries' = ListPair.zipEq (eqs, holeBoundaries)

        val w = alpha 0

        val box = Syn.into @@ Syn.BOX {dir=dir, cap=holeCap, boundaries=holeBoundaries'}
      in
        |>: goalCap
         >:+ goalBoundaries
         >:+ genInterBoundaryGoalsExceptDiag H ((holeBoundaries', holeBoundaries'), (tyBoundaries, NONE, K.top))
         >:+ genCapBoundaryGoals H ((holeCap, (dir, tyTubes, holeBoundaries)), (tyCap, NONE, K.top))
         >:+ genInterTubeGoals H w ((tyTubes, tyTubes), l, kTube)
         >:+ genCapTubeGoalsIfDifferent H ((tyCap, (#1 dir, tyTubes)), NONE, K.top)
        #> (H, box)
      end

    (* TODO Add the Elim, EqCap and Eta rules. *)
  end

  structure V =
  struct
    val kindConstraintOnEnds =
      fn K.DISCRETE => E.raiseError @@
          E.NOT_APPLICABLE (Fpp.text "V types", Fpp.text "discrete universes")
       | K.KAN => (K.KAN, K.KAN)
       | K.HCOM => (K.HCOM, K.HCOM) (* XXX more research needed *)
       | K.COE => (K.COE, K.COM) (* XXX more research needed *)
       | K.STABLE => (K.STABLE, K.STABLE)

    fun intoHasAllPathsTo C c =
      let
        val c' = Var.named "c'"
        val dummy = Sym.named "_"
      in
        Syn.into @@ Syn.FUN (C, c',
          Syn.into @@ Syn.PATH ((dummy, C), VarKit.toExp c', c))
      end

    fun intoIsContr C =
      let
        val center = Var.named "center"
      in
        Syn.intoProd [(center, C)] @@ intoHasAllPathsTo C (VarKit.toExp center)
      end

    fun intoFiber A B f b =
      let
        val a = Var.named "a"
        val dummy = Sym.named "_"
      in
        Syn.intoProd [(a, A)] @@
          Syn.into @@ Syn.PATH
            ((dummy, B), Syn.intoApp (f, VarKit.toExp a), b)
      end

    fun intoIsEquiv A B f =
      let
        val b = Var.named "b"
      in
        Syn.into @@ Syn.FUN
          (B, b, intoIsContr (intoFiber A B f (VarKit.toExp b)))
      end

    fun intoEquiv A B =
      let
        val f = Var.named "f"
        val dummy = Var.named "_"
      in
        Syn.intoProd [(f, Syn.into @@ Syn.FUN (A, dummy, B))] @@
          intoIsEquiv A B (VarKit.toExp f)
      end

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "V.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.V (r0, a0, b0, e0) = Syn.out ty0
        val Syn.V (r1, a1, b1, e1) = Syn.out ty1
        val () = Assert.alphaEq' "V.EqType" (r0, r1)
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r0, Syn.into Syn.DIM0)

        val goalA = Restriction.makeEqType [eq] H ((a0, a1), l, kA)
        val goalB = makeEqType H ((b0, b1), l, kB)
        val goalEquiv = Restriction.makeEq [eq] H ((e0, e1), (intoEquiv a0 b0, NONE, K.top))
      in
        |>:? goalEquiv >:? goalA >: goalB #> (H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "V.Eq"
        val H >> AJ.EQ ((in0, in1), (ty, l, k)) = jdg
        val Syn.V (r, a, b, e) = Syn.out ty
        val Syn.VIN (r0, m0, n0) = Syn.out in0
        val Syn.VIN (r1, m1, n1) = Syn.out in1
        val () = Assert.alphaEq' "V.Eq" (r0, r1)
        val () = Assert.alphaEq' "V.Eq" (r0, r)
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r0, Syn.into Syn.DIM0)

        val goalM = Restriction.makeEq [eq] H ((m0, m1), (a, l, kA))
        val goalN = makeEq H ((n0, n1), (b, l, kB))
        val goalCoh = Restriction.makeEqIfDifferent [eq] H
          ((Syn.intoApp (Syn.into @@ Syn.PROJ (O.indexToLabel 0, e), m0), n0), (b, NONE, K.top))
        val goalEquiv = Restriction.makeMem [eq] H (e, (intoEquiv a b, NONE, K.top))
      in
        |>:? goalM >: goalN >:? goalCoh >:? goalEquiv #> (H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "V.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.V (r, a, b, e) = Syn.out ty
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r, Syn.into Syn.DIM0)

        val (goalM, holeM) = Restriction.makeTrue [eq] (Syn.into Syn.AX) H (a, l, kA)
        val (goalN, holeN) = makeTrue H (b, l, kB)
        val goalCoh = Restriction.makeEqIfDifferent [eq] H
          ((Syn.intoApp (Syn.into @@ Syn.PROJ (O.indexToLabel 0, e), holeM), holeN), (b, NONE, K.top))
        val goalEquiv = Restriction.makeMem [eq] H (e, (intoEquiv a b, NONE, K.top))
      in
        |>:? goalM >: goalN >:? goalCoh >:? goalEquiv
        #> (H, Syn.into @@ Syn.VIN (r, holeM, holeN))
      end

    (* TODO Add the Elim, EqProj and Eta rules. *)
  end

  structure Universe =
  struct
    open Universe

    (* The following should be equivalent to
     * `L.<= (inherentLevel l', l) andalso K.<= (inherentKind k', k)`
     *)
    fun member (l', k') (l, k) = L.< (l', l) andalso K.<= (inherentKind k', k)

    structure Assert =
    struct
      open Assert
      fun univMem (l0,k0) (l1,k1) =
        if member (l0,k0) (l1,k1) then ()
        else E.raiseError @@ E.GENERIC
          [Fpp.hvsep
            [Fpp.text "Expected universe", L.pretty l0, TermPrinter.ppKind k0,
             Fpp.text "be at level", L.pretty l1, Fpp.text "with kind", TermPrinter.ppKind k1]]
    end

    (* XXX needs double-checking *)
    val kindConstraint =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.KAN
       | K.COE => K.STABLE
       | K.STABLE => K.STABLE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.EqType"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty0
        val Syn.UNIVERSE (l1, k1) = Syn.out ty1
        val _ = Assert.levelEq (l0, l1)
        val _ = Assert.levelNotOmega l0
        val _ = Assert.kindEq (k0, k1)
        val _ = Assert.univMem (l0, k0) (l, k)
      in
        T.empty #> (H, trivial)
      end

    fun Eq _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.Eq"
        val H >> AJ.EQ ((a, b), (ty, l, k)) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty
        val _ = Assert.univMem (l0, k0) (l, k)

        (* l0 is not omega because of Assert.univMem *)
        val goal = makeEqType H ((a, b), l0, k0)
      in
        |>: goal #> (H, trivial)
      end

    fun True _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.True"
        val H >> AJ.TRUE (ty, l, k) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty
        val _ = Assert.univMem (l0, k0) (l, k)

        val (goalTy, holeTy) = makeTerm H O.EXP
        (* l0 is not omega because of Assert.univMem *)
        val goalTy' = makeType H (holeTy, l0, k0)
      in
        |>: goalTy >: goalTy' #> (H, Syn.into Syn.AX)
      end

    (* This rule will be removed once every hypothesis
     * is required to be `A true`. *)
    fun ElimFromTrue z alpha jdg =
      let
        val _ = RedPrlLog.trace "Universe.ElimFromTrue"
        val H >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val AJ.TRUE (ty, _, _) = Hyps.lookup H z
        val Syn.UNIVERSE (l, k) = Syn.out ty

        val u = alpha 0
        val (goal, hole) =
          makeGoal
            @@ (Hyps.interposeAfter (z, |@> (u, AJ.TYPE (VarKit.toExp z, l, k))) H)
            >> catjdg
      in
        |>: goal #> (H, VarKit.subst (trivial, u) hole)
      end

    (* This rule will also be removed once every hypothesis
     * is required to be `A true`. *)
    fun ElimFromEq z alpha jdg =
      let
        val _ = RedPrlLog.trace "Universe.ElimFromEq"
        val H >> catjdg = jdg
        (* for now we ignore the kind and the level in the context *)
        val AJ.EQ ((ty1, ty2), (univ, _, _)) = Hyps.lookup H z
        val Syn.UNIVERSE (l, k) = Syn.out univ

        val u = alpha 0
        val (goal, hole) =
          makeGoal
            @@ (Hyps.interposeAfter (z, |@> (u, AJ.EQ_TYPE ((ty1, ty2), l, k))) H)
            >> catjdg
      in
        |>: goal #> (H, VarKit.subst (trivial, u) hole)
      end

    fun Elim z = (Lcf.rule o ElimFromTrue z) orelse_ (Lcf.rule o ElimFromEq z)

    fun SubUniverse _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.SubUniverse"
        val H >> AJ.SUB_UNIVERSE (univ, l, k) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out univ
        val _ = Assert.levelLeq (l0, l)
        val _ = Assert.levelNotOmega l0
        val _ = Assert.kindLeq (k0, k)
      in
        T.empty #> (H, trivial)
      end

    (* ty0 = ty1 in (U l k) >> ty0 = ty1 at l with k *)
    (* this is for non-deterministic search *)
    fun NondetEqTypeFromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.NondetEqTypeFromEq"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val AJ.EQ ((ty0', ty1'), (univ, _, _)) = Hyps.lookup H z
        val Syn.UNIVERSE (l', k') = Syn.out univ
        val _ = Assert.alphaEqEither ((ty0', ty1'), ty0)
        val _ = Assert.alphaEqEither ((ty0', ty1'), ty1)
        val _ = Assert.levelLeq (l', l)
        val _ = Assert.kindLeq (k', k)
      in
        T.empty #> (H, trivial)
      end

    (* (= (U l k) ty0 ty1) >> ty0 = ty1 at l with k *)
    (* this is for non-deterministic search *)
    fun NondetEqTypeFromTrueEqType z _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.NondetEqTypeFromEq"
        val H >> AJ.EQ_TYPE ((ty0, ty1), l, k) = jdg
        val AJ.TRUE (eq, _, _) = Hyps.lookup H z
        val Syn.EQUALITY (univ, ty0', ty1') = Syn.out eq
        val Syn.UNIVERSE (l', k') = Syn.out univ
        val _ = Assert.alphaEqEither ((ty0', ty1'), ty0)
        val _ = Assert.alphaEqEither ((ty0', ty1'), ty1)
        val _ = Assert.levelLeq (l', l)
        val _ = Assert.kindLeq (k', k)
      in
        T.empty #> (H, trivial)
      end

    (* ty0 = ty1 at l >> ty ~~> (U l) *)
    (* this is for non-deterministic search *)
    fun NondetSynthFromEqType z _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.NondetSynthFromEqType"
        val H >> AJ.SYNTH (ty2, l2, k2) = jdg
        val AJ.EQ_TYPE ((ty0, ty1), l0, k0) = Hyps.lookup H z
        val _ = Assert.alphaEqEither ((ty0, ty1), ty2)
        (* TODO maybe generating a subgoal when it's not a member? *)
        val _ = Assert.univMem (l0, k0) (l2, k2)
      in
        (* l0 is not omega because of univMem *)
        T.empty #> (H, Syn.intoU (l0, k0))
      end

    (* (= ty m n) at l >> ty synth ~~> (U l) *)
    (* this is for non-deterministic search *)
    fun NondetSynthFromTrueEqAtType z _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.NondetSynthFromTrueEqAtType"
        val H >> AJ.SYNTH (ty1, l1, k1) = jdg
        val AJ.TRUE (eq, l0, _) = Hyps.lookup H z
        val Syn.EQUALITY (ty0, _, _) = Syn.out eq
        val _ = Assert.alphaEq (ty0, ty1)
        (* TODO maybe generating a subgoal when it's not a member? *)
        val _ = Assert.univMem (l0, K.top) (l1, k1)
      in
        (* l0 is not omega because of univMem *)
        T.empty #> (H, Syn.intoU (l0, K.top))
      end

    (* m = n in ty at l >> ty synth ~~> (U l) *)
    (* this is for non-deterministic search *)
    fun NondetSynthFromEqAtType z _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.NondetSynthFromEqAtType"
        val H >> AJ.SYNTH (ty1, l1, k1) = jdg
        val AJ.EQ (_, (ty0, l0, k0)) = Hyps.lookup H z
        val _ = Assert.alphaEq (ty0, ty1)
        val _ = Assert.univMem (l0, k0) (l1, k1)
      in
        (* l0 is not omega because of univMem *)
        T.empty #> (H, Syn.intoU (l0, k0))
      end

    (* ty at l >> ty synth ~~> (U l) *)
    (* this is for non-deterministic search *)
    fun NondetSynthFromTrueAtType z _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.NondetSynthFromTrueAtType"
        val H >> AJ.SYNTH (ty1, l1, k1) = jdg
        val AJ.TRUE (ty0, l0, k0) = Hyps.lookup H z
        val _ = Assert.alphaEq (ty0, ty1)
        (* TODO maybe generating a subgoal when it's not a member? *)
        val _ = Assert.univMem (l0, k0) (l1, k1)
      in
        (* l0 is not omega because of univMem *)
        T.empty #> (H, Syn.intoU (l0, k0))
      end

    fun VarFromTrue _ jdg =
      let
        val _ = RedPrlLog.trace "Universe.VarFromTrue"
        val H >> AJ.EQ_TYPE ((ty1, ty2), l1, k1) = jdg
        val Syn.VAR (x1, _) = Syn.out ty1
        val Syn.VAR (x2, _) = Syn.out ty2
        val _ = Assert.varEq (x1, x2)
        val AJ.TRUE (univ0, _, _) = Hyps.lookup H x1
        val Syn.UNIVERSE (l0, k0) = Syn.out univ0

        val goal = makeTypeUnlessSubUniv H (ty1, l1, k1) (l0, k0)
      in
        |>:? goal #> (H, trivial)
      end
  end
end
