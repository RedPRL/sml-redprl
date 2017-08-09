(* type-specific modules *)
functor RefinerTypeRules (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  open RedPrlAbt Kit ComRefinerKit

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = (Sym.t, abt) CJ.jdg
  type opid = Sig.opid

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix orelse_

  (* order of rules:
   *
   * EqType
   * EqX
   * True
   * Eta
   * Elim
   * EqElim
   *)

  structure Bool =
  struct
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), k) = jdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqTT"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.BOOL = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.BOOL = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    (* This is an induction on the full sequent, justified by
     * the semantics of open judgments.
     *
     * We mimicked Nuprl to keep the variable z in the subgoals.
     *)
    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.Elim"
        val (I, H) >> CJ.TRUE (cz, k) = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
        val Syn.BOOL = Syn.out ty

        (* tt branch *)
        val tt = Syn.into Syn.TT
        val Htt = Hyps.substAfter (z, tt) H
        val (goalT, holeT) = makeTrue (I, Htt) (substVar (tt, z) cz, k)

        (* ff branch *)
        val ff = Syn.into Syn.FF
        val Hff = Hyps.substAfter (z, ff) H
        val (goalF, holeF) = makeTrue (I, Hff) (substVar (ff, z) cz, k)

        val if_ = Syn.into @@ Syn.IF (VarKit.toExp z, (holeT, holeF))
      in
        |>: goalT >: goalF #> (I, H, if_)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected strict bool elimination problem"]

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Bool.EqElim"
        val (I, H) >> CJ.EQ ((if0, if1), (ty, k)) = jdg
        val Syn.IF (m0, (t0, f0)) = Syn.out if0
        val Syn.IF (m1, (t1, f1)) = Syn.out if1

        (* motive *)
        val x = alpha 0
        val Hx = H @> (x, CJ.TRUE (Syn.into Syn.BOOL, inherentKind))
        val (goalTy, holeTy) = makeTerm (I, Hx) O.EXP
        val goalTy' = makeType (I, Hx) (holeTy, k)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (Syn.into Syn.WBOOL, K.top))

        (* result type*)
        val goalTy0 = makeEqTypeIfDifferent (I, H) ((substVar (m0, x) holeTy, ty), k)

        (* tt branch *)
        val goalT = makeEq (I, H) ((t0, t1), (substVar (Syn.into Syn.TT, x) holeTy, K.top))

        (* ff branch *)
        val goalF = makeEq (I, H) ((f0, f1), (substVar (Syn.into Syn.FF, x) holeTy, K.top))
      in
        |>: goalTy >: goalM >: goalT >: goalF >:? goalTy0 >: goalTy' #> (I, H, trivial)
      end

    (* This is an induction on the full sequent, justified by
     * the semantics of open judgments *)
    fun TrivialByElim z _ jdg =
      let
        val _ = RedPrlLog.trace "Bool.TrivialByElim"
        val (I, H) >> catjdg = jdg
        val true = CJ.synthesis catjdg = O.TRIV
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
        val Syn.BOOL = Syn.out ty

        (* tt branch *)
        val tt = Syn.into Syn.TT
        val Htt = Hyps.substAfter (z, tt) H
        val goalT = makeGoal' @@ (I, Htt) >> CJ.map_ (substVar (tt, z)) catjdg

        (* ff branch *)
        val ff = Syn.into Syn.FF
        val Hff = Hyps.substAfter (z, ff) H
        val goalF = makeGoal' @@ (I, Hff) >> CJ.map_ (substVar (ff, z)) catjdg
      in
        |>: goalT >: goalF #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected strict bool elimination problem"]
  end

  structure WBool =
  struct
    val inherentKind = K.KAN

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), k) = jdg
        val Syn.WBOOL = Syn.out a
        val Syn.WBOOL = Syn.out b
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqTT"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFF _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqFF"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqFCom alpha jdg =
      let
        val _ = RedPrlLog.trace "WBool.EqFCom"
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, k)) = jdg
        val Syn.WBOOL = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs
      in
        ComKit.EqFComDelegator alpha (I, H) args0 args1 (ty, k)
      end

    (* We are not doing an induction on the full sequent because of FCOM *)
    fun Elim z _ jdg =
      let
        val _ = RedPrlLog.trace "WBool.Elim"
        val (I, H) >> CJ.TRUE (cz, k) = jdg
        (* if(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
        val Syn.WBOOL = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType (I, H) (cz, k)

        (* tt branch *)
        val (goalT, holeT) = makeTrue (I, H) (substVar (Syn.into Syn.TT, z) cz, K.top)

        (* ff branch *)
        val (goalF, holeF) = makeTrue (I, H) (substVar (Syn.into Syn.FF, z) cz, K.top)

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
        val (I, H) >> CJ.EQ ((if0, if1), (ty, k)) = jdg
        (* if(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.WIF ((x, c0x), m0, (t0, f0)) = Syn.out if0
        val Syn.WIF ((y, c1y), m1, (t1, f1)) = Syn.out if1

        (* motive *)
        val z = alpha 0
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val goalTy = makeEqType (I, H @> (z, CJ.TRUE (Syn.into Syn.WBOOL, inherentKind))) ((c0z, c1z), K.top)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (Syn.into Syn.WBOOL, K.top))

        (* result type*)
        val goalTy0 = makeEqTypeIfDifferentOrLess (I, H) ((substVar (m0, x) c0x, ty), k) K.top

        (* tt branch *)
        val goalT = makeEq (I, H) ((t0, t1), (substVar (Syn.into Syn.TT, x) c0x, K.top))

        (* ff branch *)
        val goalF = makeEq (I, H) ((f0, f1), (substVar (Syn.into Syn.FF, x) c0x, K.top))
      in
        |>: goalM >: goalT >: goalF >:? goalTy0 >: goalTy #> (I, H, trivial)
      end
  end

  structure Nat =
  struct
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), k) = jdg
        val Syn.NAT = Syn.out a
        val Syn.NAT = Syn.out b
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqZero"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.NAT = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqSucc"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.NAT = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq (I, H) ((m', n'), (Syn.into Syn.NAT, K.top))
      in
        |>: goal #> (I, H, trivial)
      end

    (* We are not doing an induction on the full sequent because of recursion *)
    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.Elim"
        val (I, H) >> CJ.TRUE (cz, k) = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
        val Syn.NAT = Syn.out ty

        val nat = Syn.into Syn.NAT

        (* zero branch *)
        val czero = substVar (Syn.into Syn.ZERO, z) cz
        val (goalZ, holeZ) = makeTrue (I, H) (czero, k)

        (* succ branch *)
        val u = alpha 0
        val v = alpha 1
        val cu = VarKit.rename (u, z) cz
        val Hsucc = H @> (u, CJ.TRUE (nat, inherentKind)) @> (v, CJ.TRUE (cu, k))
        val csuccu = substVar (Syn.into @@ Syn.SUCC @@ VarKit.toExp u, z) cz
        val (goalS, holeS) = makeTrue (I, Hsucc) (csuccu, k)

        (* realizer *)
        val evidence = Syn.into @@ Syn.NAT_REC (VarKit.toExp z, (holeZ, (u, v, holeS)))
      in
        |>: goalZ >: goalS #> (I, H, evidence)
      end

    fun EqElim alpha jdg =
      let
        val _ = RedPrlLog.trace "Nat.EqElim"
        val (I, H) >> CJ.EQ ((elim0, elim1), (ty, k)) = jdg
        val Syn.NAT_REC (m0, (n0, (a0, b0, p0))) = Syn.out elim0
        val Syn.NAT_REC (m1, (n1, (a1, b1, p1))) = Syn.out elim1

        val nat = Syn.into Syn.NAT

        (* motive *)
        val z = alpha 0
        val (goalC, holeC) = makeTerm (I, H @> (z, CJ.TRUE (nat, inherentKind))) O.EXP
        val goalC' = makeType (I, H @> (z, CJ.TRUE (nat, inherentKind))) (holeC, k)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (nat, K.top))

        (* result type *)
        val goalTy = makeEqTypeIfDifferent (I, H) ((substVar (m0, z) holeC, ty), k)

        (* zero branch *)
        val czero = substVar (Syn.into Syn.ZERO, z) holeC
        val goalZ = makeEq (I, H) ((n0, n1), (czero, K.top))

        (* succ branch *)
        val x = alpha 1
        val y = alpha 2
        val cu = VarKit.rename (x, z) holeC
        val csuccu = substVar (Syn.into @@ Syn.SUCC @@ VarKit.toExp x, z) holeC
        val p0 = VarKit.renameMany [(x, a0), (y, b0)] p0
        val p1 = VarKit.renameMany [(x, a1), (y, b1)] p1
        val goalS =
          makeEq
            (I, H @> (x, CJ.TRUE (nat, inherentKind)) @> (y, CJ.TRUE (cu, k)))
            ((p0, p1), (csuccu, K.top))
      in
        |>: goalC >: goalM >: goalZ >: goalS >: goalC' >:? goalTy #> (I, H, trivial)
      end
  end

  structure Int =
  struct
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), k) = jdg
        val Syn.INT = Syn.out a
        val Syn.INT = Syn.out b
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqZero"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqSucc"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq (I, H) ((m', n'), (Syn.into Syn.NAT, K.top))
      in
        |>: goal #> (I, H, trivial)
      end

    fun EqNegSucc _ jdg =
      let
        val _ = RedPrlLog.trace "Int.EqNegSucc"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.INT = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.NEGSUCC m' = Syn.out m
        val Syn.NEGSUCC n' = Syn.out n
        val goal = makeEq (I, H) ((m', n'), (Syn.into Syn.NAT, K.top))
      in
        |>: goal #> (I, H, trivial)
      end
  end

  structure Void =
  struct
    val inherentKind = K.DISCRETE

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Void.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), k) = jdg
        val Syn.VOID = Syn.out a
        val Syn.VOID = Syn.out b
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
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
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
    val inherentKind = K.KAN

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqType"
        val (I, H) >> CJ.EQ_TYPE ((a, b), k) = jdg
        val Syn.S1 = Syn.out a
        val Syn.S1 = Syn.out b
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqBase _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqBase"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.BASE = Syn.out m
        val Syn.BASE = Syn.out n
      in
        T.empty #> (I, H, trivial)
      end

    fun EqLoop _ jdg =
      let
        val _ = RedPrlLog.trace "S1.EqLoop"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.S1 = Syn.out ty
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
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, k)) = jdg
        val Syn.S1 = Syn.out ty
        val _ = Assert.kindLeq (inherentKind, k)
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs
      in
        ComKit.EqFComDelegator alpha (I, H) args0 args1 (ty, K.top)
      end

    (* We are not doing an induction on the full sequent because of FCOM *)
    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "S1.Elim"
        val (I, H) >> CJ.TRUE (cz, k) = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
        val Syn.S1 = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType (I, H) (cz, k)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, z) cz
        val (goalB, holeB) = makeTrue (I, H) (cbase, K.top)

        (* loop branch *)
        val u = alpha 0
        val loop = Syn.into o Syn.LOOP @@ P.ret u
        val cloop = substVar (loop, z) cz
        val (goalL, holeL) = makeTrue (I @ [(u,P.DIM)], H) (cloop, K.top)

        (* coherence *)
        val l0 = substSymbol (P.APP P.DIM0, u) holeL
        val l1 = substSymbol (P.APP P.DIM1, u) holeL
        val goalCoh0 = makeEqIfDifferent (I, H) ((l0, holeB), (cbase, K.top)) (* holeB well-typed *)
        val goalCoh1 = makeEqIfAllDifferent (I, H) ((l1, holeB), (cbase, K.top)) [l0]

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
        val (I, H) >> CJ.EQ ((elim0, elim1), (ty, k)) = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.meet (k, K.COM)
        val Syn.S1_REC ((x, c0x), m0, (b0, (u, l0u))) = Syn.out elim0
        val Syn.S1_REC ((y, c1y), m1, (b1, (v, l1v))) = Syn.out elim1

        val S1 = Syn.into Syn.S1

        (* motive *)
        val z = alpha 0
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val goalC = makeEqType (I, H @> (z, CJ.TRUE (S1, inherentKind))) ((c0z, c1z), k)

        (* eliminated term *)
        val goalM = makeEq (I, H) ((m0, m1), (S1, K.top))

        (* result type *)
        val goalTy = makeEqTypeIfDifferent (I, H) ((substVar (m0, x) c0x, ty), k) (* c0m0 type *)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, x) c0x
        val goalB = makeEq (I, H) ((b0, b1), (cbase, K.top))

        (* loop branch*)
        val w = alpha 1
        val l0w = substSymbol (P.ret w, u) l0u
        val l1w = substSymbol (P.ret w, v) l1v
        val cloop = substVar (Syn.into @@ Syn.LOOP (P.ret w), x) c0x
        val goalL = makeEq (I @ [(w,P.DIM)], H) ((l0w, l1w), (cloop, K.top))

        (* coherence *)
        val l00 = substSymbol (P.APP P.DIM0, u) l0u
        val l01 = substSymbol (P.APP P.DIM1, u) l0u
        val goalCoh0 = makeEqIfAllDifferent (I, H) ((l00, b0), (cbase, K.top)) [b1]
        val goalCoh1 = makeEqIfAllDifferent (I, H) ((l01, b0), (cbase, K.top)) [l00, b1]
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
       | K.HCOM => (K.top, K.HCOM)
       | K.COE => (K.COE, K.COE)
       | K.CUBICAL => (K.CUBICAL, K.CUBICAL)

    fun EqType alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.EqType"
        val (I, H) >> CJ.EQ_TYPE ((dfun0, dfun1), k) = jdg
        val Syn.DFUN (a0, x, b0x) = Syn.out dfun0
        val Syn.DFUN (a1, y, b1y) = Syn.out dfun1
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = makeEqType (I, H) ((a0, a1), ka)

        (* codomain *)
        val z = alpha 0
        val b0z = VarKit.rename (z, x) b0x
        val b1z = VarKit.rename (z, y) b1y
        val goalB = makeEqType (I, H @> (z, CJ.TRUE (a0, ka))) ((b0z, b1z), kb)
      in
        |>: goalA >: goalB #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected dfun typehood sequent"]

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Eq"
        val (I, H) >> CJ.EQ ((lam0, lam1), (dfun, k)) = jdg
        val Syn.LAM (x, m0x) = Syn.out lam0
        val Syn.LAM (y, m1y) = Syn.out lam1
        val Syn.DFUN (a, z, bz) = Syn.out dfun
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = makeType (I, H) (a, ka)

        (* function *)
        val w = alpha 0
        val m0w = VarKit.rename (w, x) m0x
        val m1w = VarKit.rename (w, y) m1y
        val bw = VarKit.rename (w, z) bz
        val goalM = makeEq (I, H @> (w, CJ.TRUE (a, ka))) ((m0w, m1w), (bw, kb))
      in
        |>: goalM >: goalA #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.True"
        val (I, H) >> CJ.TRUE (dfun, k) = jdg
        val Syn.DFUN (a, x, bx) = Syn.out dfun
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain*)
        val goalA = makeType (I, H) (a, ka)

        (* function *)
        val z = alpha 0
        val bz = VarKit.rename (z, x) bx
        val (goalLam, hole) = makeTrue (I, H @> (z, CJ.TRUE (a, ka))) (bz, kb)

        (* realizer *)
        val lam = Syn.into @@ Syn.LAM (z, hole)
      in
        |>: goalLam >: goalA #> (I, H, lam)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected dfun truth sequent"]

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "DFun.Eta"
        val (I, H) >> CJ.EQ ((m, n), (dfun, k)) = jdg
        val Syn.DFUN (_, x, _) = Syn.out dfun

        val m' = Syn.into @@ Syn.LAM (x, Syn.into @@ Syn.APP (m, VarKit.toExp x))
        val goal1 = makeMem (I, H) (m, (dfun, k))
        val goal2 = makeEq (I, H) ((m', n), (dfun, K.top))
      in
        |>: goal1 >: goal2 #> (I, H, trivial)
      end

    fun Elim z alpha jdg =
      let
        val _ = RedPrlLog.trace "DFun.Elim"
        val (I, H) >> CJ.TRUE (cz, k) = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (dfun, _) = Hyps.lookup z H
        val Syn.DFUN (a, x, bx) = Syn.out dfun

        (* argument *)
        val (goalA, holeA) = makeTrue (I, H) (a, K.top)

        (* new context *)
        val b' = substVar (holeA, x) bx
        val u = alpha 0
        val v = alpha 1
        val aptm = Syn.into @@ Syn.APP (VarKit.toExp z, holeA)
        (* note: a and bx come from the telescope so they are types *)
        val H' = |@> (u, CJ.TRUE (b', K.top)) @> (v, CJ.EQ ((VarKit.toExp u, aptm), (b', K.top)))
        val H'' = Hyps.interposeAfter (z, H') H
        val (goalF, holeF) = makeTrue (I, H'') (cz, k)
      in
        |>: goalA >: goalF #> (I, H, VarKit.substMany [(aptm, u), (trivial, v)] holeF)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "DFun.EqApp"
        val (I, H) >> CJ.EQ ((ap0, ap1), (ty, k)) = jdg
        val Syn.APP (m0, n0) = Syn.out ap0
        val Syn.APP (m1, n1) = Syn.out ap1

        val (goalDFun, holeDFun) = makeSynth (I, H) (m0, K.top)
        val (goalDom, holeDom) = makeMatch (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeMatch (O.MONO O.DFUN, 1, holeDFun, [], [n0])
        val goalFunEq = makeEqIfDifferent (I, H) ((m0, m1), (holeDFun, K.top))
        val goalArgEq = makeEq (I, H) ((n0, n1), (holeDom, K.top))
        val goalTyEq = makeEqTypeIfDifferentOrLess (I, H) ((holeCod, ty), k) K.top
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

    fun EqType _ jdg =
      let
        val _ = RedPrlLog.trace "Record.EqType"
        val (I, H) >> CJ.EQ_TYPE ((record0, record1), k) = jdg
        val Syn.RECORD fields0 = Syn.out record0
        val Syn.RECORD fields1 = Syn.out record1
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        val {goals, ...} =
          ListPair.foldlEq
            (fn (((lbl0, var0), ty0), ((lbl1, var1), ty1), {goals, hyps, ren0, ren1, isFirst}) =>
               let
                 val () = Assert.labelEq "Record.EqType" (lbl0, lbl1)
                 val var = Var.named lbl0
                 val ty0' = renameVars ren0 ty0
                 val ty1' = renameVars ren1 ty1
                 val kind = if isFirst then headKind else tailKind
                 val goals' = goals >: makeEqType (I, hyps) ((ty0', ty1'), kind)
                 val hyps' = hyps @> (var, CJ.TRUE (ty0', kind))
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
        val (I, H) >> CJ.EQ ((tuple0, tuple1), (record, k)) = jdg
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
                 val goals' = goals >: makeEq (I, H) ((m0, m1), (ty', kind))
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType (I, hyps) (ty, kind)
                 val hyps' = hyps @> (var, CJ.TRUE (ty, kind))
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
        val (I, H) >> CJ.TRUE (record, k) = jdg
        val Syn.RECORD fields = Syn.out record
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        val {goals, famGoals, elements, ...} =
          List.foldl
            (fn (((lbl, var), ty), {goals, famGoals, elements, env, hyps, isFirst}) =>
               let
                 val kind = if isFirst then headKind else tailKind
                 val hyps' = hyps @> (var, CJ.TRUE (ty, kind))
                 val ty' = substVarenv env ty
                 val (elemGoal, elemHole) = makeTrue (I, H) (ty', kind)
                 val env' = Var.Ctx.insert env var elemHole
                 val goals' = goals >: elemGoal
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType (I, hyps) (ty, kind)
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
        val (I, H) >> CJ.EQ ((m, n), (record, k)) = jdg
        val Syn.RECORD rcd = Syn.out record
        val dom = List.map (#1 o #1) rcd

        fun goLabel lbl = ([],[]) \ (Syn.into @@ Syn.PROJ (lbl, m))

        val m' = O.MONO (O.TUPLE dom) $$ List.map goLabel dom
        val goal1 = makeMem (I, H) (m, (record, k))
        val goal2 = makeEqIfDifferent (I, H) ((m', n), (record, k)) (* m' well-typed *)
      in
        |>: goal1 >:? goal2 #> (I, H, trivial)
      end

    fun MatchRecord _ jdg =
      let
        val _ = RedPrlLog.trace "Record.MatchRecord"
        val MATCH_RECORD (lbl, tm) = jdg

        val Abt.$ (O.MONO (O.RECORD lbls), args) = Abt.out tm

        val (_ \ arg) = List.nth (args, #1 (Option.valOf (ListUtil.findEqIndex lbl lbls)))
      in
        Lcf.|> (T.empty, abtToAbs arg)
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH_RECORD judgment failed to unify"]

    fun EqProj _ jdg =
      let
        val _ = RedPrlLog.trace "Record.EqProj"
        val (I, H) >> CJ.EQ ((proj0, proj1), (ty, k)) = jdg
        val Syn.PROJ (lbl0, m0) = Syn.out proj0
        val Syn.PROJ (lbl1, m1) = Syn.out proj1
        val () = Assert.labelEq "Record.EqProj" (lbl0, lbl1)

        val (goalTy, holeTy) = makeSynth (I, H) (m0, K.top)
        val (goalTyP, holeTyP) = makeMatchRecord (lbl0, holeTy)
        val goalEq = makeEqIfDifferent (I, H) ((m0, m1), (holeTy, K.top)) (* m0 well-typed *)
        val goalEqTy = makeEqTypeIfDifferentOrLess (I, H) ((holeTyP, ty), k) K.top (* holeTyP type *)
      in
        |>: goalTy >: goalTyP >:? goalEq >:? goalEqTy
        #> (I, H, trivial)
      end

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Record.Elim"
        val (I, H) >> CJ.TRUE (motivez, k) = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (record, _) = Hyps.lookup z H
        val Syn.RECORD fields = Syn.out record

        val names = List.tabulate (List.length fields, alpha)
        val {hyps, ...} =
          ListPair.foldlEq
            (fn (name, ((_, var), ty), {ren, hyps}) =>
              {ren = Var.Ctx.insert ren var name,
               hyps = hyps @> (name, CJ.TRUE (renameVars ren ty, K.top))})
            {ren = Var.Ctx.empty, hyps = Hyps.empty}
            (names, fields)
        val tuple = Syn.into @@ Syn.TUPLE @@
          ListPair.mapEq
            (fn (((lbl, _), _), name) => (lbl, Syn.into @@ Syn.VAR (name, O.EXP)))
            (fields, names)
        val H' = Hyps.interposeThenSubstAfter (z, hyps, tuple) H

        val motive' = substVar (tuple, z) motivez
        val (goal, hole) = makeTrue (I,  H') (motive', k)

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
        val (I, H) >> CJ.EQ_TYPE ((ty0, ty1), k) = jdg
        val Syn.PATH_TY ((u, a0u), m0, n0) = Syn.out ty0
        val Syn.PATH_TY ((v, a1v), m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val w = alpha 0
        val a0w = substSymbol (P.ret w, u) a0u
        val a1w = substSymbol (P.ret w, v) a1v
        val tyGoal = makeEqType (I @ [(w,P.DIM)], H) ((a0w, a1w), ka)

        val a00 = substSymbol (P.APP P.DIM0, u) a0u
        val a01 = substSymbol (P.APP P.DIM1, u) a0u
        val goal0 = makeEq (I, H) ((m0, m1), (a00, K.top))
        val goal1 = makeEq (I, H) ((n0, n1), (a01, K.top))
      in
        |>: tyGoal >: goal0 >: goal1 #> (I, H, trivial)
      end

    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.Eq"
        val (I, H) >> CJ.EQ ((abs0, abs1), (ty, k)) = jdg
        val Syn.PATH_TY ((u, au), p0, p1) = Syn.out ty
        val ka = kindConstraintOnBase k
        val Syn.PATH_ABS (v, m0v) = Syn.out abs0
        val Syn.PATH_ABS (w, m1w) = Syn.out abs1

        val z = alpha 0
        val az = substSymbol (P.ret z, u) au
        val m0z = substSymbol (P.ret z, v) m0v
        val m1z = substSymbol (P.ret z, w) m1w
        val goalM = makeEq (I @ [(z,P.DIM)], H) ((m0z, m1z), (az, ka))

        val a0 = substSymbol (P.APP P.DIM0, u) au
        val a1 = substSymbol (P.APP P.DIM1, u) au
        val m00 = substSymbol (P.APP P.DIM0, v) m0v
        val m01 = substSymbol (P.APP P.DIM1, v) m0v
        (* note: m00 and m01 are well-typed and az is well-kinded  *)
        val goalCoh0 = makeEqIfDifferent (I, H) ((m00, p0), (a0, K.top))
        val goalCoh1 = makeEqIfDifferent (I, H) ((m01, p1), (a1, K.top))
      in
        |>: goalM >:? goalCoh0 >:? goalCoh1 #> (I, H, trivial)
      end

    fun True alpha jdg =
      let
        val _ = RedPrlLog.trace "Path.True"
        val (I, H) >> CJ.TRUE (ty, k) = jdg
        val Syn.PATH_TY ((u, au), p0, p1) = Syn.out ty
        val ka = kindConstraintOnBase k
        val a0 = substSymbol (P.APP P.DIM0, u) au
        val a1 = substSymbol (P.APP P.DIM1, u) au

        val v = alpha 0
        val av = substSymbol (P.ret v, u) au
        val (mainGoal, mhole) = makeTrue (I @ [(v,P.DIM)], H) (av, ka)

        (* note: m0 and m1 are already well-typed *)
        val m0 = substSymbol (P.APP P.DIM0, v) mhole
        val m1 = substSymbol (P.APP P.DIM1, v) mhole
        val goalCoh0 = makeEqIfDifferent (I, H) ((m0, p0), (a0, K.top))
        val goalCoh1 = makeEqIfDifferent (I, H) ((m1, p1), (a1, K.top))

        val abstr = Syn.into @@ Syn.PATH_ABS (v, mhole)
      in
        |>: mainGoal >:? goalCoh0 >:? goalCoh1 #> (I, H, abstr)
      end

    fun Eta _ jdg =
      let
        val _ = RedPrlLog.trace "Path.Eta"
        val (I, H) >> CJ.EQ ((m, n), (pathTy, k)) = jdg
        val Syn.PATH_TY ((u, _), _, _) = Syn.out pathTy

        val m' = Syn.into @@ Syn.PATH_ABS (u, Syn.into @@ Syn.PATH_APP (m, P.ret u))
        val goal1 = makeMem (I, H) (m, (pathTy, k))
        val goal2 = makeEqIfDifferent (I, H) ((m', n), (pathTy, K.top)) (* m' will-typed *)
      in
        |>: goal1 >:? goal2 #> (I, H, trivial)
      end

    fun Elim z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Path.Elim"

        val (I, H) >> CJ.TRUE (motive, k) = jdg
        (* for now we ignore the kind in the context *)
        val CJ.TRUE (ty, _) = Hyps.lookup z H
        val Syn.PATH_TY ((u, a), _, _) = Syn.out ty

        val x = alpha 0
        val y = alpha 1
        
        val (dimGoal, dimHole) = makeTerm (I, H) @@ O.PARAM_EXP O.DIM
        val (arGoal, arHole) = makeDimSubst (I, H) (dimHole, u, a)

        val w = Sym.named "w"
        val (pathAppGoal, pathAppHole) = makeDimSubst (I, H) (dimHole, w, Syn.into @@ Syn.PATH_APP (VarKit.toExp z, P.ret w))

        val H' = |@> (x, CJ.TRUE (arHole, K.top)) @> (y, CJ.EQ ((VarKit.toExp x, pathAppHole), (arHole, K.top)))
        val H'' = Hyps.interposeAfter (z, H') H
        val (mainGoal, mainHole) = makeTrue (I, H'') (motive, k)
      in
        |>: dimGoal >: arGoal >: pathAppGoal >: mainGoal
        #> (I, H, VarKit.substMany [(pathAppHole, x), (trivial, y)] mainHole)
      end

    fun EqApp _ jdg =
      let
        val _ = RedPrlLog.trace "Path.EqApp"
        val (I, H) >> CJ.EQ ((ap0, ap1), (ty, k)) = jdg
        val Syn.PATH_APP (m0, r0) = Syn.out ap0
        val Syn.PATH_APP (m1, r1) = Syn.out ap1
        val () = Assert.paramEq "Path.EqApp" (r0, r1)

        val (goalSynth, holeSynth) = makeSynth (I, H) (m0, K.top)
        val goalMem = makeEqIfDifferent (I, H) ((m0, m1), (holeSynth, K.top)) (* m0 well-typed *)
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holeSynth, [r0], [])
        val goalTy = makeEqTypeIfDifferentOrLess (I, H) ((holeLine, ty), k) K.top (* holeLine type *)
      in
        |>: goalSynth >:? goalMem >: goalLine >:? goalTy #> (I, H, trivial)
      end

    fun EqAppConst _ jdg =
      let
        val _ = RedPrlLog.trace "Path.EqAppConst"
        val (I, H) >> CJ.EQ ((ap, p), (a, k)) = jdg
        val Syn.PATH_APP (m, P.APP r) = Syn.out ap
        val (goalSynth, holeSynth) = makeSynth (I, H) (m, K.top)

        val dimAddr = case r of P.DIM0 => 1 | P.DIM1 => 2
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holeSynth, [P.APP r], [])
        val (goalEndpoint, holeEndpoint) = makeMatch (O.MONO O.PATH_TY, dimAddr, holeSynth, [], [])
        val goalTy = makeEqTypeIfDifferent (I, H) ((holeLine, a), K.top) (* holeLine should be well-typed *)
        val goalEq = makeEq (I, H) ((holeEndpoint, p), (a, k))
      in
        |>: goalSynth >: goalLine >: goalEndpoint >:? goalTy >: goalEq
        #> (I, H, trivial)
      end
  end
end
