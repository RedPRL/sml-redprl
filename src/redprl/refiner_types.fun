(* type-specific modules *)
functor RefinerTypeRules (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  open RedPrlAbt Kit ComRefinerKit

  type sign = Sig.sign
  type rule = Lcf.jdg Lcf.tactic
  type ajdg = AJ.jdg
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
   *
   *   Rule ordering:
   *     well-typed of the eliminated terms
   *     well-typed of the branches
   *     coherence among branches
   *     well-kinded of the type
   *     well-kinded of the motive
   *     subtyping for the resulting type
   * BetaX: the beta rule for the eliminator applied to a constructor X.
   *   This is only necessary in cases where the reduction is unstable.
   * EqTypeElim/EqTypeX: similar to EqElim but for EQ_TYPE judgments.
   * (others): other special rules for this type.
   *)

  (* The order of aux goals:
   *
   * 1. Well-typedness of interesting parts.
   *   1a. Eliminated term
   *   1b. Branches
   *   1c. Coherence for 1a and 1b.
   * 2. Motives.
   *   2a. Types.
   *   2b. Coherence for 2a.
   * 3. Rules for synthesizing the types.
   * 4. Subtyping for the final type.
   *)

structure Synth =
  struct
    infix $ $$ \

    local
      fun synthNeutral' sign tr H (tm1, tm2) =
        case (out tm1, out tm2) of
          (`x, `y) =>
            let
              val true = Var.eq (x, y)
              val AJ.TRUE ty = Hyps.lookup H x
            in
              ([], ty)
            end

          | (O.CUST (opid, _) $ args, O.CUST (opid', _) $ args') =>
            let
              val true = Abt.eq (tm1, tm2)
              val AJ.TRUE ty = Sig.theoremSpec sign opid args
            in
              ([], ty)
            end

          | (O.APP $ [_ \ m1, _ \ m2], O.APP $ [_ \ n1, _ \ n2]) =>
            let
              val (psi, funty) = synthTerm' sign tr H (m1, n1)
              val Syn.FUN (dom, x, cod) = Syn.out funty
              val memGoal = makeEq tr H ((m2, n2), dom)
            in
              (memGoal :: psi, substVar (m2, x) cod)
            end

          | (O.DIM_APP $ [_ \ m, _ \ r], O.DIM_APP $ [_ \ n, _ \ s]) =>
            let
              val true = Abt.eq (r, s)
              val (psi, ty) = synthTerm' sign tr H (m, n)
            in
              case Syn.out ty of
                Syn.PATH ((x, a), _, _) =>
                (psi, substVar (r, x) a)

              | Syn.LINE (x, a) =>
                (psi, substVar (r, x) a)

              | _ => raise Fail "synthNeutral"
            end

          | (O.DIM_APP $ [_ \ m, _ \ r], _) =>
            let
              val (psi, pathty) = synthTerm' sign tr H (m, m)
              val Syn.PATH ((x, a), left, right) = Syn.out pathty
              val n =
                case Syn.out r of
                   Syn.DIM0 => left
                 | Syn.DIM1 => right
              val ty = substVar (r, x) a
              val goal = makeEq tr H ((n, tm2), ty)
            in
              (goal :: psi, ty)
            end

          | (_, O.DIM_APP $ [_ \ m, _ \ r]) =>
            let
              val (psi, pathty) = synthTerm' sign tr H (m, m)
              val Syn.PATH ((x, a), left, right) = Syn.out pathty
              val n =
                case Syn.out r of
                   Syn.DIM0 => left
                 | Syn.DIM1 => right
              val ty = substVar (r, x) a
              val goal = makeEq tr H ((tm1, n), ty)
            in
              (goal :: psi, ty)
            end

          | (O.PROJ lbl $ [_ \ m], O.PROJ lbl' $ [_ \ n]) =>
            let
              val true = lbl = lbl'
              val (psi, rcdty) = synthTerm' sign tr H (m, n)
              val Abt.$ (O.RECORD lbls, args) = out rcdty

              val i = #1 (Option.valOf (ListUtil.findEqIndex lbl lbls))
              val (us \ ty) = List.nth (args, i)

              (* supply the dependencies *)
              val lblPrefix = List.take (lbls, i)
              val rho = ListPair.mapEq (fn (lbl, u) => (Syn.into @@ Syn.PROJ (lbl, m), u)) (lblPrefix, us)
              val ty = VarKit.substMany rho ty
            in
              (psi, ty)
            end

          | (O.S1_REC $ [[x] \ cx, _ \ m, _, _], O.S1_REC $ _) =>
            let
              val ty = substVar (m, x) cx
              val goal = makeEq tr H ((tm1, tm2), ty)
            in
              ([goal], ty)
            end

          | (O.IF $ [[x] \ cx, _ \ m, _, _], O.IF $ _) =>
            let
              val ty = substVar (m, x) cx
              val goal = makeEq tr H ((tm1, tm2), ty)
            in
              ([goal], ty)
            end

          | (O.PUSHOUT_REC $ [[x] \ cx, _ \ m, _, _, _], O.PUSHOUT_REC $ _) =>
            let
              val ty = substVar (m, x) cx
              val goal = makeEq tr H ((tm1, tm2), ty)
            in
              ([goal], ty)
            end

          | (O.COEQUALIZER_REC $ [[x] \ cx, _ \ m, _, _], O.COEQUALIZER_REC $ _) =>
            let
              val ty = substVar (m, x) cx
              val goal = makeEq tr H ((tm1, tm2), ty)
            in
              ([goal], ty)
            end

          | (O.NAT_REC $ [[x] \ cx, _ \ m, _, _], O.NAT_REC $ _) =>
            let
              val ty = substVar (m, x) cx
              val goal = makeEq tr H ((tm1, tm2), ty)
            in
              ([goal], ty)
            end
          | (O.INT_REC $ [[x] \ cx, _ \ m, _, _, _, _], O.INT_REC $ _) =>
            let
              val ty = substVar (m, x) cx
              val goal = makeEq tr H ((tm1, tm2), ty)
            in
              ([goal], ty)
            end

      and synthTerm' sign tr H (tm1, tm2) =
        let
          val (psi, ty) = synthNeutral' sign tr H (Machine.eval sign Machine.STABLE Machine.Unfolding.never tm1, Machine.eval sign Machine.STABLE Machine.Unfolding.never tm2)
        in
          (psi, Machine.eval sign Machine.STABLE Machine.Unfolding.always ty)
        end

    in
      fun synthNeutral sign tr H (tm1, tm2) =
        let
          val (psi, ty) = synthNeutral' sign tr H (tm1, tm2)
        in
          (List.rev psi, ty)
        end
      
      fun synthTerm sign tr H (tm1, tm2) =
        let
          val (psi, ty) = synthTerm' sign tr H (tm1, tm2)
        in
          (List.rev psi, ty)
        end
    end
  end

  structure Bool =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType jdg =
      let
        val H >> ajdg = jdg
        val ((a, b), l, k) = View.matchAsEqType ajdg
        val Syn.BOOL = Syn.out a
        val Syn.BOOL = Syn.out b
        val _ = View.Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT jdg =
      let
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.BOOL = Syn.out ty
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun EqFF jdg =
      let
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.BOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["Bool.Elim"]
        val H >> AJ.TRUE cz = jdg
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.BOOL = Syn.out ty

        (* tt branch *)
        val tt = Syn.into Syn.TT
        val Htt = Hyps.substAfter (z, tt) H
        val (goalT, holeT) = makeTrue tr Htt (substVar (tt, z) cz)

        (* ff branch *)
        val ff = Syn.into Syn.FF
        val Hff = Hyps.substAfter (z, ff) H
        val (goalF, holeF) = makeTrue tr Hff (substVar (ff, z) cz)

        val evidence = Syn.into @@ Syn.IF ((z, cz), VarKit.toExp z, (holeT, holeF))
      in
        |>: goalT >: goalF #> (H, evidence)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected strict bool elimination problem"]

    fun EqElim sign jdg =
      let
        val tr = ["Bool.EqElim"]
        val H >> ajdg = jdg
        val ((if0, if1), ty) = View.matchAsEq ajdg
        val Syn.IF ((z, motivez), m0, (t0, f0)) = Syn.out if0
        val Syn.IF (_, m1, (t1, f1)) = Syn.out if1

        val (psi, boolTy) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.BOOL = Syn.out boolTy

        (* result type*)
        val goalTy = View.makeAsSubType tr H (substVar (m0, z) motivez, ty)

        (* tt branch *)
        val goalT = makeEq tr H ((t0, t1), (substVar (Syn.into Syn.TT, z) motivez))

        (* ff branch *)
        val goalF = makeEq tr H ((f0, f1), (substVar (Syn.into Syn.FF, z) motivez))
      in
        |>: goalT >: goalF >:+ psi >: goalTy #> (H, axiom)
      end
  end

  structure WBool =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.KAN

    fun EqType jdg =
      let
        val tr = ["WBool.EqType"]
        val H >> ajdg = jdg
        val ((a, b), l, k) = View.matchAsEqType ajdg
        val Syn.WBOOL = Syn.out a
        val Syn.WBOOL = Syn.out b
        val _ = View.Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqTT jdg =
      let
        val tr = ["WBool.EqTT"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.WBOOL = Syn.out ty
        val Syn.TT = Syn.out m
        val Syn.TT = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun EqFF jdg =
      let
        val tr = ["WBool.EqFF"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.WBOOL = Syn.out ty
        val Syn.FF = Syn.out m
        val Syn.FF = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun EqFCom jdg =
      let
        val tr = ["WBool.EqFCom"]
        val H >> ajdg = jdg
        val ((lhs, rhs), ty) = View.matchTrueAsEq ajdg
        val Syn.WBOOL = Syn.out ty
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs

        val w = Sym.new ()
      in
        |>:+ (ComKit.genEqFComGoals tr H w (args0, args1) ty)
        #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["WBool.Elim"]
        val H >> AJ.TRUE cz = jdg
        (* if(FCOM) steps to COM *)
        val k = K.COM
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.WBOOL = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType tr H (cz, k)

        (* tt branch *)
        val (goalT, holeT) = makeTrue tr H (substVar (Syn.into Syn.TT, z) cz)

        (* ff branch *)
        val (goalF, holeF) = makeTrue tr H (substVar (Syn.into Syn.FF, z) cz)

        (* realizer *)
        val if_ = Syn.into @@ Syn.IF ((z, cz), VarKit.toExp z, (holeT, holeF))
      in
        |>: goalT >: goalF >: goalKind #> (H, if_)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected bool elimination problem"]

    fun EqElim sign jdg =
      let
        val tr = ["WBool.EqElim"]
        val H >> ajdg = jdg
        val ((if0, if1), ty) = View.matchAsEq ajdg
        (* if(FCOM) steps to COM *)
        val k = K.COM
        val Syn.IF ((x, c0x), m0, (t0, f0)) = Syn.out if0
        val Syn.IF ((y, c1y), m1, (t1, f1)) = Syn.out if1

        val (psi, wboolTy) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.WBOOL = Syn.out wboolTy

        (* motive *)
        val z = Sym.new ()
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val Hz = H @> (z, AJ.TRUE (Syn.into Syn.WBOOL))
        val goalC = makeEqType tr Hz ((c0z, c1z), k)

        (* result type*)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (substVar (m0, x) c0x, ty)

        (* tt branch *)
        val goalT = makeEq tr H ((t0, t1), (substVar (Syn.into Syn.TT, x) c0x))

        (* ff branch *)
        val goalF = makeEq tr H ((f0, f1), (substVar (Syn.into Syn.FF, x) c0x))
      in
        |>: goalT >: goalF >: goalC >:+ psi >:? goalTy #> (H, axiom)
      end
  end

  structure Nat =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType jdg =
      let
        val tr = ["Nat.EqType"]
        val H >> ajdg = jdg
        val ((a, b), l, k) = View.matchAsEqType ajdg
        val Syn.NAT = Syn.out a
        val Syn.NAT = Syn.out b
        val _ = View.Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero jdg =
      let
        val tr = ["Nat.EqZero"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.NAT = Syn.out ty
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun EqSucc jdg =
      let
        val tr = ["Nat.EqSucc"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.NAT = Syn.out ty
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq tr H ((m', n'), Syn.into Syn.NAT)
      in
        |>: goal #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["Nat.Elim"]      
        val H >> AJ.TRUE cz = jdg
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.NAT = Syn.out ty

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* zero branch *)
        val (goalZ, holeZ) = makeTrue tr H (substVar (zero, z) cz)

        (* succ branch *)
        val u = Sym.new ()
        val v = Sym.new ()
        val cu = VarKit.rename (u, z) cz
        val (goalS, holeS) =
          makeTrue
            tr
            (H @> (u, AJ.TRUE nat) @> (v, AJ.TRUE cu))
            (substVar (succ @@ VarKit.toExp u, z) cz)

        (* realizer *)
        val evidence = Syn.into @@ Syn.NAT_REC ((z, cz), VarKit.toExp z, (holeZ, (u, v, holeS)))
      in
        |>: goalZ >: goalS #> (H, evidence)
      end

    fun EqElim jdg =
      let
        val tr = ["Nat.EqElim"]
        val H >> ajdg = jdg
        val ((elim0, elim1), ty) = View.matchAsEq ajdg
        val Syn.NAT_REC ((x, c0x), m0, (n0, (a0, b0, p0))) = Syn.out elim0
        val Syn.NAT_REC ((y, c1y), m1, (n1, (a1, b1, p1))) = Syn.out elim1

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC

        (* motive *)
        val z = Sym.new ()
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y
        val Hz = H @> (z, AJ.TRUE nat)
        val goalC = makeEqType tr Hz ((c0z, c1z), K.top)

        (* eliminated term *)
        val goalM = makeEq tr H ((m0, m1), nat)

        (* result type *)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (substVar (m0, x) c0x, ty)

        (* zero branch *)
        val goalZ = makeEq tr H ((n0, n1), (substVar (zero, x) c0x))

        (* succ branch *)
        val u = Sym.new ()
        val v = Sym.new ()
        val cu = VarKit.rename (u, x) c0x
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            tr
            (H @> (u, AJ.TRUE nat) @> (v, AJ.TRUE cu))
            ((p0, p1), (substVar (succ @@ VarKit.toExp u, x) c0x))
      in
        |>: goalM >: goalZ >: goalS >: goalC >:? goalTy #> (H, axiom)
      end
  end

  structure Int =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType jdg =
      let
        val tr = ["Int.EqType"]
        val H >> ajdg = jdg
        val ((a, b), l, k) = View.matchAsEqType ajdg
        val Syn.INT = Syn.out a
        val Syn.INT = Syn.out b
        val _ = View.Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqZero jdg =
      let
        val tr = ["Int.EqZero"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.INT = Syn.out ty
        val Syn.ZERO = Syn.out m
        val Syn.ZERO = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun EqSucc jdg =
      let
        val tr = ["Int.EqSucc"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.INT = Syn.out ty
        val Syn.SUCC m' = Syn.out m
        val Syn.SUCC n' = Syn.out n
        val goal = makeEq tr H ((m', n'), Syn.into Syn.NAT)
      in
        |>: goal #> (H, axiom)
      end

    fun EqNegSucc jdg =
      let
        val tr = ["Int.EqNegSucc"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.INT = Syn.out ty
        val Syn.NEGSUCC m' = Syn.out m
        val Syn.NEGSUCC n' = Syn.out n
        val goal = makeEq tr H ((m', n'), Syn.into Syn.NAT)
      in
        |>: goal #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["Int.Elim"]
        val H >> AJ.TRUE cz = jdg
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.INT = Syn.out ty

        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC
        val negsucc = Syn.into o Syn.NEGSUCC

        (* zero branch *)
        val (goalZ, holeZ) = makeTrue tr H (substVar (zero, z) cz)

        (* succ branch *)
        val u = Sym.new ()
        val v = Sym.new ()
        val cu = VarKit.rename (u, z) cz
        val (goalS, holeS) =
          makeTrue
            tr
            (H @> (u, AJ.TRUE nat) @> (v, AJ.TRUE cu))
            (substVar (succ @@ VarKit.toExp u, z) cz)

        (* (negsucc zero) branch *)
        val (goalNSZ, holeNSZ) = makeTrue tr H (substVar (negsucc zero, z) cz)

        (* (negsucc succ) branch *)
        val cnegsuccu = Abt.substVar (negsucc @@ VarKit.toExp u, z) cz
        val (goalNSS, holeNSS) =
          makeTrue
            tr
            (H @> (u, AJ.TRUE nat) @> (v, AJ.TRUE cnegsuccu))
            (substVar (negsucc @@ succ @@ VarKit.toExp u, z) cz)

        (* realizer *)
        val evidence = Syn.into @@ Syn.INT_REC ((z, cz), VarKit.toExp z, (holeZ, (u, v, holeS), holeNSZ, (u, v, holeNSS)))
      in
        |>: goalZ >: goalS >: goalNSZ >: goalNSS #> (H, evidence)
      end

    fun EqElim jdg =
      let
        val tr = ["Int.EqElim"]
        val H >> ajdg = jdg
        val ((elim0, elim1), ty) = View.matchAsEq ajdg
        val Syn.INT_REC ((x, e0x), m0, (n0, (a0, b0, p0), q0, (c0, d0, r0))) = Syn.out elim0
        val Syn.INT_REC ((y, e1y), m1, (n1, (a1, b1, p1), q1, (c1, d1, r1))) = Syn.out elim1

        val int = Syn.into Syn.INT
        val nat = Syn.into Syn.NAT
        val zero = Syn.into Syn.ZERO
        val succ = Syn.into o Syn.SUCC
        val negsucc = Syn.into o Syn.NEGSUCC

        (* motive *)
        val z = Sym.new ()
        val e0z = VarKit.rename (z, x) e0x
        val e1z = VarKit.rename (z, y) e1y
        val Hz = H @> (z, AJ.TRUE int)
        val goalE = makeEqType tr Hz ((e0z, e1z), K.top)

        (* eliminated term *)
        val goalM = makeEq tr H ((m0, m1), int)

        (* result type *)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (substVar (m0, x) e0x, ty)

        (* zero branch *)
        val goalZ = makeEq tr H ((n0, n1), (substVar (zero, x) e0x))

        (* succ branch *)
        val u = Sym.new ()
        val v = Sym.new ()
        val cu = VarKit.rename (u, x) e0x
        val p0 = VarKit.renameMany [(u, a0), (v, b0)] p0
        val p1 = VarKit.renameMany [(u, a1), (v, b1)] p1
        val goalS =
          makeEq
            tr
            (H @> (u, AJ.TRUE nat) @> (v, AJ.TRUE cu))
            ((p0, p1), substVar (succ @@ VarKit.toExp u, x) e0x)

        (* (negsucc zero) branch *)
        val goalNSZ = makeEq tr H ((q0, q1), substVar (negsucc zero, x) e0x)

        (* (negsucc succ) branch *)
        val cnegsuccu = Abt.substVar (negsucc @@ VarKit.toExp u, x) e0x
        val r0 = VarKit.renameMany [(u, c0), (v, d0)] r0
        val r1 = VarKit.renameMany [(u, c1), (v, d1)] r1
        val goalNSS =
          makeEq
            tr
            (H @> (u, AJ.TRUE nat) @> (v, AJ.TRUE cnegsuccu))
            ((r0, r1), substVar (negsucc @@ succ @@ VarKit.toExp u, x) e0x)
      in
        |>: goalM >: goalZ >: goalS >: goalNSZ >: goalNSS >: goalE >:? goalTy #> (H, axiom)
      end
  end

  structure Void =
  struct
    val inherentLevel = L.zero
    val inherentKind = K.DISCRETE

    fun EqType jdg =
      let
        val tr = ["Void.EqType"]
        val H >> ajdg = jdg
        val ((a, b), l, k) = View.matchAsEqType ajdg
        val Syn.VOID = Syn.out a
        val Syn.VOID = Syn.out b
        val _ = View.Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun Elim z jdg =
      let
        val tr = ["Void.Elim"]
        val H >> ajdg = jdg
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.VOID = Syn.out ty

        val evidence =
          case ajdg of
             AJ.TRUE _ => axiom
           | AJ.EQ_TYPE _ => axiom
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

    fun EqType jdg =
      let
        val tr = ["S1.EqType"]
        val H >> ajdg = jdg
        val ((a, b), l, k) = View.matchAsEqType ajdg
        val Syn.S1 = Syn.out a
        val Syn.S1 = Syn.out b
        val _ = View.Assert.levelLeq (inherentLevel, l)
        val _ = Assert.kindLeq (inherentKind, k)
      in
        T.empty #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected typehood sequent"]

    fun EqBase jdg =
      let
        val tr = ["S1.EqBase"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.S1 = Syn.out ty
        val Syn.BASE = Syn.out m
        val Syn.BASE = Syn.out n
      in
        T.empty #> (H, axiom)
      end

    fun EqLoop jdg =
      let
        val tr = ["S1.EqLoop"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.S1 = Syn.out ty
        val Syn.LOOP r1 = Syn.out m
        val Syn.LOOP r2 = Syn.out n
        val () = Assert.alphaEq' "S1.EqLoop" (r1, r2)
      in
        T.empty #> (H, axiom)
      end

    fun EqFCom jdg =
      let
        val tr = ["S1.EqFCom"]
        val H >> ajdg = jdg
        val ((lhs, rhs), ty) = View.matchTrueAsEq ajdg
        val Syn.S1 = Syn.out ty
        val Syn.FCOM args0 = Syn.out lhs
        val Syn.FCOM args1 = Syn.out rhs

        val w = Sym.new ()
      in
        |>:+ (ComKit.genEqFComGoals tr H w (args0, args1) ty)
        #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["S1.Elim"]
        val H >> AJ.TRUE cz = jdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.COM
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.S1 = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType tr H (cz, k)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, z) cz
        val (goalB, holeB) = makeTrue tr H cbase

        (* loop branch *)
        val u = Sym.new ()
        val loop = Syn.into o Syn.LOOP @@ VarKit.toDim u
        val cloop = substVar (loop, z) cz
        val (goalL, holeL) = makeTrue tr (H @> (u, AJ.TERM O.DIM)) cloop

        (* coherence *)
        val l0 = substVar (Syn.into Syn.DIM0, u) holeL
        val l1 = substVar (Syn.into Syn.DIM1, u) holeL
        val goalCoh0 = makeEq tr H ((l0, holeB), cbase)
        val goalCoh1 = makeEqIfAllDifferent tr H ((l1, holeB), cbase) [l0] (* l0 well-typed *)

        (* realizer *)
        val elim = Syn.into @@ Syn.S1_REC ((z, cz), VarKit.toExp z, (holeB, (u, holeL)))
      in
        |>: goalB >: goalL >: goalCoh0 >:? goalCoh1 >: goalKind #> (H, elim)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected circle elimination problem"]

    fun EqElim jdg =
      let
        val tr = ["S1.EqElim"]
        val H >> ajdg = jdg
        val ((elim0, elim1), ty) = View.matchAsEq ajdg
        (* S1-rec(FCOM) steps to COM *)
        val k = K.COM
        val Syn.S1_REC ((x, c0x), m0, (b0, (u, l0u))) = Syn.out elim0
        val Syn.S1_REC ((y, c1y), m1, (b1, (v, l1v))) = Syn.out elim1

        val S1 = Syn.into Syn.S1

        (* motive *)
        val z = Sym.new ()
        val c0z = VarKit.rename (z, x) c0x
        val c1z = VarKit.rename (z, y) c1y

        val goalC = makeEqType tr (H @> (z, AJ.TRUE S1)) ((c0z, c1z), k)

        (* eliminated term *)
        val goalM = makeEq tr H ((m0, m1), S1)

        (* result type *)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (substVar (m0, x) c0x, ty)

        (* base branch *)
        val cbase = substVar (Syn.into Syn.BASE, x) c0x
        val goalB = makeEq tr H ((b0, b1), cbase)

        (* loop branch*)
        val w = Sym.new ()
        val l0w = substVar (VarKit.toDim w, u) l0u
        val l1w = substVar (VarKit.toDim w, v) l1v
        val cloop = substVar (Syn.into @@ Syn.LOOP (VarKit.toDim w), x) c0x
        val goalL = makeEq tr (H @> (w, AJ.TERM O.DIM)) ((l0w, l1w), cloop)

        (* coherence *)
        val l00 = substVar (Syn.into Syn.DIM0, u) l0u
        val l01 = substVar (Syn.into Syn.DIM1, u) l0u
        val goalCoh0 = makeEqIfAllDifferent tr H ((l00, b0), cbase) [b1]
        val goalCoh1 = makeEqIfAllDifferent tr H ((l01, b0), cbase) [l00, b1]
      in
        |>: goalM >: goalB >: goalL >:? goalCoh0 >:? goalCoh1 >: goalC >:? goalTy
        #> (H, axiom)
      end

    fun BetaLoop jdg =
      let
        val tr = ["S1.BetaLoop"]
        val H >> ajdg = jdg

        val ((elim, m), ty) = View.matchAsEq ajdg
        val Syn.S1_REC (_, n, (b, (u, lu))) = Syn.out elim
        val Syn.LOOP r = Syn.out n

        (* reduced goal *)
        val lr = substVar (r, u) lu
        val goalRed = View.makeAsEq tr H ((lr, m), ty)

        (* coherence *)
        val l0 = substVar (Syn.intoDim 0, u) lu
        val goalCoh0 = Restriction.View.makeAsEqIfAllDifferent tr [(r, Syn.intoDim 0)] H ((b, m), ty) [l0]
        val l1 = substVar (Syn.intoDim 1, u) lu
        val goalCoh1 = Restriction.View.makeAsEqIfAllDifferent tr [(r, Syn.intoDim 1)] H ((b, m), ty) [l1]
      in
        |>: goalRed >:? goalCoh0 >:? goalCoh1 #> (H, axiom)
      end
  end

  structure MultiArrow = 
  struct
    datatype arg =
       EXP_ARG of variable * abt
     | DIM_ARG of variable

    fun reduce sign =
      Machine.eval sign Machine.STABLE (Machine.Unfolding.default sign)

    fun stripFunTy sign n ty = 
      case n of 
         0 => ([], ty)
       | _ =>
         (case Syn.out (reduce sign ty) of 
             Syn.FUN (a, x, bx) =>
             let
               val (args, rest) = stripFunTy sign (n - 1) bx
             in
               (EXP_ARG (x,a) :: args, rest)
             end

           | Syn.PATH ((u, a), _, _) => 
             let
               val (args, rest) = stripFunTy sign (n - 1) a
             in
               (DIM_ARG u :: args, rest)
             end

           | Syn.LINE (u, a) => 
             let
               val (args, rest) = stripFunTy sign (n - 1) a
             in
               (DIM_ARG u :: args, rest)
             end             

           | _ => raise Fail "stripFunTy")

    fun Elim sign 0 z jdg = Lcf.ret Lcf.isjdg jdg
      | Elim sign (n : int) z jdg = 
      let
        val tr = ["Fun.MultiElim"]
        val H >> ajdg = jdg
        val AJ.TRUE ty = Hyps.lookup H z
        val (args, rest) = stripFunTy sign n ty

        val {goals = argGoals, env, aptm} = 
          List.foldl
            (fn (EXP_ARG (x, a), {goals, env, aptm}) =>
                let
                  val (goal, hole) = makeTrue tr H @@ substVarenv env a
                  val goals' = goals >: goal
                  val env' = Var.Ctx.insert env x hole
                  val aptm' = Syn.into @@ Syn.APP (aptm, hole)                
                in
                  {goals = goals', env = env', aptm = aptm'}                
                end
              | (DIM_ARG u, {goals, env, aptm}) =>
                let
                  val (goal, hole) = makeTerm tr H O.DIM
                  val goals' = goals >: goal
                  val env' = Var.Ctx.insert env u hole
                  val aptm' = Syn.into @@ Syn.DIM_APP (aptm, hole)
                in
                  {goals = goals', env = env', aptm = aptm'}
                end)
            {goals = T.empty, env = Var.Ctx.empty, aptm = VarKit.toExp z}
            args

        val rest' = substVarenv env rest

        val u = Sym.new ()
        val v = Sym.new ()

        val H' = Hyps.interposeAfter
          (z, |@> (u, AJ.TRUE rest')
               @> (v, AJ.EQ ((VarKit.toExp u, aptm), rest')))
          H

        val (mainGoal, mainHole) = makeGoal tr @@ H' >> ajdg
      in
        argGoals >: mainGoal #> (H, VarKit.substMany [(aptm, u), (axiom, v)] mainHole)
      end  
  end


  structure Fun =
  struct
    val kindConstraintsOnDomAndCod =
      fn K.DISCRETE => (K.DISCRETE, K.DISCRETE)
       | K.KAN => (K.COE, K.KAN)
       | K.HCOM => (K.PRE, K.HCOM)
       | K.COE => (K.COE, K.COE)
       | K.PRE => (K.PRE, K.PRE)

    fun EqType jdg =
      let
        val tr = ["Fun.EqType"]
        val H >> ajdg = jdg
        val ((fun0, fun1), l, k) = View.matchAsEqType ajdg
        val Syn.FUN (a0, x, b0x) = Syn.out fun0
        val Syn.FUN (a1, y, b1y) = Syn.out fun1
        val (ka, kb) = kindConstraintsOnDomAndCod k

        (* domain *)
        val goalA = View.makeAsEqType tr H ((a0, a1), l, ka)

        (* codomain *)
        val z = Sym.new ()
        val b0z = VarKit.rename (z, x) b0x
        val b1z = VarKit.rename (z, y) b1y
        val goalB = View.makeAsEqType tr (H @> (z, AJ.TRUE a0)) ((b0z, b1z), l, kb)
      in
        |>: goalA >: goalB #> (H, axiom)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected fun typehood sequent"]

    fun Eq jdg =
      let
        val tr = ["Fun.Eq"]
        val H >> ajdg = jdg
        val ((lam0, lam1), ty) = View.matchTrueAsEq ajdg
        val Syn.LAM (x, m0x) = Syn.out lam0
        val Syn.LAM (y, m1y) = Syn.out lam1
        val Syn.FUN (a, z, bz) = Syn.out ty

        (* domain *)
        val goalA = makeType tr H (a, K.top)

        (* function *)
        val w = Sym.new ()
        val m0w = VarKit.rename (w, x) m0x
        val m1w = VarKit.rename (w, y) m1y
        val bw = VarKit.rename (w, z) bz
        val goalM = makeEq tr (H @> (w, AJ.TRUE a)) ((m0w, m1w), bw)
      in
        |>: goalM >: goalA #> (H, axiom)
      end

    fun True jdg =
      let
        val tr = ["Fun.True"]
        val H >> AJ.TRUE ty = jdg
        val Syn.FUN (a, x, bx) = Syn.out ty

        (* domain*)
        val goalA = makeType tr H (a, K.top)

        (* function *)
        val z = Sym.new ()
        val bz = VarKit.rename (z, x) bx
        val (goalLam, hole) = makeTrue tr (H @> (z, AJ.TRUE a)) bz

        (* realizer *)
        val lam = Syn.intoLam (z, hole)
      in
        |>: goalLam >: goalA #> (H, lam)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected fun truth sequent"]

    fun Eta jdg =
      let
        val tr = ["Fun.Eta"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.FUN (_, x, _) = Syn.out ty

        val m' = Syn.intoLam (x, Syn.intoApp (m, VarKit.toExp x))
        val goal1 = makeMem tr H (m, ty)
        val goal2 = makeEqIfDifferent tr H ((m', n), ty)
      in
        |>:? goal2 >: goal1 #> (H, axiom)
      end

    fun EqApp sign jdg =
      let
        val tr = ["Fun.EqApp"]
        val H >> ajdg = jdg
        val ((ap0, ap1), ty) = View.matchAsEq ajdg
        val Syn.APP (m0, n0) = Syn.out ap0
        val Syn.APP (m1, n1) = Syn.out ap1
        val (psi, funTy) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.FUN (dom, x, codx) = Syn.out funTy
        val cod = substVar (n0, x) codx
        val goalArgEq = makeEq tr H ((n0, n1), dom)
        val goalTy = View.makeAsSubType tr H (cod, ty)
      in
        |>: goalArgEq >:+ psi >: goalTy
        #> (H, axiom)
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
       | K.PRE => (K.PRE, K.PRE)

    fun EqType jdg =
      let
        val tr = ["Record.EqType"]
        val H >> ajdg = jdg
        val ((record0, record1), l, k) = View.matchAsEqType ajdg
        val Syn.RECORD fields0 = Syn.out record0
        val Syn.RECORD fields1 = Syn.out record1
        val (headKind, tailKind) = kindConstraintsOnHeadAndTail k

        val {goals, ...} =
          ListPair.foldlEq
            (fn (((lbl0, var0), ty0), ((lbl1, var1), ty1), {goals, hyps, ren0, ren1, isFirst}) =>
               let
                 val () = Assert.labelEq "Record.EqType" (lbl0, lbl1)
                 val var = Sym.new ()
                 val ty0' = renameVars ren0 ty0
                 val ty1' = renameVars ren1 ty1
                 val kind = if isFirst then headKind else tailKind
                 val goals' = goals >: View.makeAsEqType tr hyps ((ty0', ty1'), l, kind)
                 val hyps' = hyps @> (var, AJ.TRUE ty0')
                 val ren0' = Var.Ctx.insert ren0 var0 var
                 val ren1' = Var.Ctx.insert ren1 var1 var
               in
                 {goals = goals', hyps = hyps', ren0 = ren0', ren1 = ren1', isFirst = false}
               end)
            {goals = T.empty, hyps = H, ren0 = Var.Ctx.empty, ren1 = Var.Ctx.empty, isFirst = true}
            (fields0, fields1)
      in
        goals #> (H, axiom)
      end

    fun Eq jdg =
      let
        val tr = ["Record.Eq"]
        val H >> ajdg = jdg
        val ((tuple0, tuple1), record) = View.matchTrueAsEq ajdg
        val Syn.RECORD fields = Syn.out record

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
                 val goals' = goals >: makeEq tr H ((m0, m1), ty')
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType tr hyps (ty, K.top)
                 (* FIXME this "var" is not accessible to the user! *)
                 val hyps' = hyps @> (var, AJ.TRUE ty)
               in
                 {goals = goals', famGoals = famGoals', env = env', hyps = hyps', isFirst = false}
               end)
            {goals = T.empty, famGoals = T.empty, env = Var.Ctx.empty, hyps = H, isFirst = true}
            fields
      in
        T.append goals famGoals #> (H, axiom)
      end

    fun EqInv z jdg =
      let
        val H >> ajdg = jdg
        val tr = ["Record.EqInv"]
        val ((m1, m2), record) = View.matchTrueAsEq (Hyps.lookup H z)
        val Syn.RECORD fields = Syn.out record

        val (hyps, _) =
          List.foldl
            (fn (field, (hyps, env)) =>
               let
                 val ((name, var), ty) = field
                 val proj1 = Syn.into @@ Syn.PROJ (name, m1)
                 val proj2 = Syn.into @@ Syn.PROJ (name, m2)
                 val x = Sym.new ()
                 val eqjdg = AJ.EQ ((proj1, proj2), substVarenv env ty)
                 val env' = Var.Ctx.insert env var proj1
               in
                 (hyps @> (x, eqjdg), env')
               end)
            (Hyps.empty, Var.Ctx.empty)
            fields

        val H' = Hyps.remove z (Hyps.interposeThenSubstAfter (z, hyps, axiom) H)
        val ajdg' = AJ.map (substVar (axiom, z)) ajdg
        val (goal, hole) = makeGoal tr @@ H' >> ajdg'
        val extractEnv = Hyps.foldl (fn (x, _, rho) => Var.Ctx.insert rho x axiom) Var.Ctx.empty hyps
      in
        |>: goal #> (H, substVarenv extractEnv hole)
      end

    fun True jdg =
      let
        val tr = ["Record.True"]
        val H >> AJ.TRUE record = jdg
        val Syn.RECORD fields = Syn.out record

        val {goals, famGoals, elements, ...} =
          List.foldl
            (fn (((lbl, var), ty), {goals, famGoals, elements, env, hyps, isFirst}) =>
               let
                 val hyps' = hyps @> (var, AJ.TRUE ty)
                 val ty' = substVarenv env ty
                 val (elemGoal, elemHole) = makeTrue tr H ty'
                 val env' = Var.Ctx.insert env var elemHole
                 val goals' = goals >: elemGoal
                 val famGoals' = if isFirst then famGoals else famGoals >: makeType tr hyps (ty, K.top)
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

    fun Eta jdg =
      let
        val tr = ["Record.Eta"]
        val H >> ajdg = jdg
        val ((m, n), record) = View.matchTrueAsEq ajdg
        val Syn.RECORD rcd = Syn.out record
        val dom = List.map (#1 o #1) rcd

        fun goLabel lbl = [] \ (Syn.into @@ Syn.PROJ (lbl, m))

        val m' = O.TUPLE dom $$ List.map goLabel dom
        val goal1 = makeMem tr H (m, record)
        val goal2 = makeEqIfDifferent tr H ((m', n), record) (* m' well-typed *)
      in
        |>:? goal2 >: goal1 #> (H, axiom)
      end

    fun Elim z jdg = 
      let
        val tr = ["Record.Elim"]
        val H >> ajdg = jdg
        val AJ.TRUE record = Hyps.lookup H z
        val Syn.RECORD fields = Syn.out record

        val names = List.tabulate (List.length fields, fn _ => Sym.new ())

        val {hyps, ...} =
          ListPair.foldlEq
            (fn (name, ((_, var), ty), {ren, hyps}) =>
              {ren = Var.Ctx.insert ren var name,
               hyps = hyps @> (name, AJ.TRUE (renameVars ren ty))})
            {ren = Var.Ctx.empty, hyps = Hyps.empty}
            (names, fields)

        val tuple = Syn.into @@ Syn.TUPLE @@
          ListPair.mapEq
            (fn (((lbl, _), _), name) => (lbl, VarKit.toExp name))
            (fields, names)

        val H' = Hyps.interposeThenSubstAfter (z, hyps, tuple) H

        val (goal, hole) = makeGoal tr @@ H' >> AJ.map (substVar (tuple, z)) ajdg

        val projEnv =
          ListPair.foldlEq
            (fn (((lbl, _), _), name, env) =>
              Var.Ctx.insert env name @@ Syn.into @@ Syn.PROJ (lbl, VarKit.toExp z))
            Var.Ctx.empty (fields, names)
      in
        |>: goal #> (H, substVarenv projEnv hole)
      end
      handle _ => raise E.error [Fpp.text "Record.Elim"]

    fun EqProj sign jdg =
      let
        val tr = ["Record.EqProj"]
        val H >> ajdg = jdg
        val ((proj0, proj1), ty) = View.matchAsEq ajdg
        val Syn.PROJ (lbl0, m0) = Syn.out proj0
        val Syn.PROJ (lbl1, m1) = Syn.out proj1
        val () = Assert.labelEq "Record.EqProj" (lbl0, lbl1)

        val (psi, rcdty) = Synth.synthTerm sign tr H (m0, m1)
        val Abt.$ (O.RECORD lbls, args) = out rcdty

        val i = #1 (Option.valOf (ListUtil.findEqIndex lbl0 lbls))
        val (us \ tyField) = List.nth (args, i)

        (* supply the dependencies *)
        val lblPrefix = List.take (lbls, i)
        val rho = ListPair.mapEq (fn (lbl, u) => (Syn.into @@ Syn.PROJ (lbl, m0), u)) (lblPrefix, us)
        val tyField = VarKit.substMany rho tyField
        
        val goalTy = View.makeAsSubType tr H (VarKit.substMany rho tyField, ty)
      in
        |>:+ psi >: goalTy
        #> (H, axiom)
      end
  end

  structure Path =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.HCOM
       | K.COE => K.KAN
       | K.PRE => K.PRE

    fun EqType jdg =
      let
        val tr = ["Path.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.PATH ((u, a0u), m0, n0) = Syn.out ty0
        val Syn.PATH ((v, a1v), m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val w = Sym.new ()
        val a0w = substVar (VarKit.toDim w, u) a0u
        val a1w = substVar (VarKit.toDim w, v) a1v
        val tyGoal = View.makeAsEqType tr (H @> (w, AJ.TERM O.DIM)) ((a0w, a1w), l, ka)

        val a00 = substVar (Syn.into Syn.DIM0, u) a0u
        val a01 = substVar (Syn.into Syn.DIM1, u) a0u
        val goal0 = makeEq tr H ((m0, m1), a00)
        val goal1 = makeEq tr H ((n0, n1), a01)
      in
        |>: tyGoal >: goal0 >: goal1 #> (H, axiom)
      end

    fun Eq jdg =
      let
        val tr = ["Path.Eq"]
        val H >> ajdg = jdg
        val ((abs0, abs1), ty) = View.matchTrueAsEq ajdg
        val Syn.PATH ((u, au), p0, p1) = Syn.out ty
        val Syn.ABS (v, m0v) = Syn.out abs0
        val Syn.ABS (w, m1w) = Syn.out abs1

        val z = Sym.new ()
        val az = substVar (VarKit.toDim z, u) au
        val m0z = substVar (VarKit.toDim z, v) m0v
        val m1z = substVar (VarKit.toDim z, w) m1w
        val goalM = makeEq tr (H @> (z, AJ.TERM O.DIM)) ((m0z, m1z), az)

        val a0 = substVar (Syn.into Syn.DIM0, u) au
        val a1 = substVar (Syn.into Syn.DIM1, u) au
        val m00 = substVar (Syn.into Syn.DIM0, v) m0v
        val m01 = substVar (Syn.into Syn.DIM1, v) m0v
        (* note: m00 and m01 are well-typed and az is well-kinded  *)
        val goalCoh0 = makeEqIfDifferent tr H ((m00, p0), a0)
        val goalCoh1 = makeEqIfDifferent tr H ((m01, p1), a1)
      in
        |>: goalM >:? goalCoh0 >:? goalCoh1 #> (H, axiom)
      end

    fun True jdg =
      let
        val tr = ["Path.True"]
        val H >> AJ.TRUE ty = jdg
        val Syn.PATH ((u, au), p0, p1) = Syn.out ty
        val a0 = substVar (Syn.into Syn.DIM0, u) au
        val a1 = substVar (Syn.into Syn.DIM1, u) au

        val v = Sym.new ()
        val av = substVar (VarKit.toDim v, u) au
        val (mainGoal, mhole) = makeTrue tr (H @> (v, AJ.TERM O.DIM)) av

        (* note: m0 and m1 are already well-typed *)
        val m0 = substVar (Syn.into Syn.DIM0, v) mhole
        val m1 = substVar (Syn.into Syn.DIM1, v) mhole
        val goalCoh0 = makeEq tr H ((m0, p0), a0)
        val goalCoh1 = makeEq tr H ((m1, p1), a1)

        val abstr = Syn.into @@ Syn.ABS (v, mhole)
      in
        |>: mainGoal >: goalCoh0 >: goalCoh1 #> (H, abstr)
      end

    fun Eta jdg =
      let
        val tr = ["Path.Eta"]
        val H >> ajdg = jdg
        val ((m, n), pathTy) = View.matchTrueAsEq ajdg
        val Syn.PATH ((u, _), _, _) = Syn.out pathTy

        val m' = Syn.into @@ Syn.ABS (u, Syn.into @@ Syn.DIM_APP (m, VarKit.toDim u))
        val goal1 = makeMem tr H (m, pathTy)
        val goal2 = makeEqIfDifferent tr H ((m', n), pathTy) (* m' will-typed *)
      in
        |>:? goal2 >: goal1 #> (H, axiom)
      end

    fun EqApp sign jdg =
      let
        val tr = ["Path.EqApp"]
        val H >> ajdg = jdg
        val ((ap0, ap1), ty) = View.matchAsEq ajdg
        val Syn.DIM_APP (m0, r0) = Syn.out ap0
        val Syn.DIM_APP (m1, r1) = Syn.out ap1
        val () = Assert.alphaEq (r0, r1)

        val (psi, pathty) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.PATH ((x, tyx), _, _) = Syn.out pathty
        val tyr = substVar (r0, x) tyx
        val goalTy = View.makeAsSubType tr H (tyr, ty) (* holePath type *)
      in
        |>:+ psi >: goalTy #> (H, axiom)
      end

 fun EqAppConst sign jdg =
      let
        val tr = ["Path.EqAppConst"]
        val H >> ajdg = jdg
        val ((ap, p), a) = View.matchAsEq ajdg
        val Syn.DIM_APP (m, r) = Syn.out ap

        val (psi, pathty) = Synth.synthTerm sign tr H (m, m)
        val Syn.PATH ((x, tyx), p0, p1) = Syn.out pathty
        val tyr = substVar (r, x) tyx
        val pr = case Syn.out r of Syn.DIM0 => p0 | Syn.DIM1 => p1 

        val goalTy = View.makeAsSubType tr H (tyr, a)
        val goalEq = View.makeAsEq tr H ((pr, p), a)
      in
        |>: goalEq >:+ psi >: goalTy
        #> (H, axiom)
      end

    fun EqFromLine jdg =
      let
        val tr = ["Path.EqFromLine"]
        val H >> ajdg = jdg
        val ((m0, m1), pathTy) = View.matchTrueAsEq ajdg
        val Syn.PATH ((x, ty), n0, n1) = Syn.out pathTy
        val dim0 = Syn.into Syn.DIM0
        val dim1 = Syn.into Syn.DIM1
        val goalLine = makeEq tr H ((m0, m1), Syn.into (Syn.LINE (x,ty)))
        val goalLeft = makeEq tr H ((n0, Syn.into (Syn.DIM_APP (m0, dim0))), substVar (dim0,x) ty)
        val goalRight = makeEq tr H ((n1, Syn.into (Syn.DIM_APP (m1, dim1))), substVar (dim1,x) ty)
      in
        |>: goalLine >: goalLeft >: goalRight #> (H, axiom)
      end
  end

  structure Line =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.KAN
       | K.HCOM => K.HCOM
       | K.COE => K.COE
       | K.PRE => K.PRE

    fun EqType jdg =
      let
        val tr = ["Line.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.LINE (u, a0u) = Syn.out ty0
        val Syn.LINE (v, a1v) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val w = Sym.new ()
        val a0w = substVar (VarKit.toDim w, u) a0u
        val a1w = substVar (VarKit.toDim w, v) a1v
        val tyGoal = View.makeAsEqType tr (H @> (w, AJ.TERM O.DIM)) ((a0w, a1w), l, ka)
      in
        |>: tyGoal #> (H, axiom)
      end

    fun Eq jdg =
      let
        val tr = ["Line.Eq"]
        val H >> ajdg = jdg
        val ((abs0, abs1), ty) = View.matchTrueAsEq ajdg
        val Syn.LINE (u, au) = Syn.out ty
        val Syn.ABS (v, m0v) = Syn.out abs0
        val Syn.ABS (w, m1w) = Syn.out abs1

        val z = Sym.new ()
        val az = substVar (VarKit.toDim z, u) au
        val m0z = substVar (VarKit.toDim z, v) m0v
        val m1z = substVar (VarKit.toDim z, w) m1w
        val goalM = makeEq tr (H @> (z, AJ.TERM O.DIM)) ((m0z, m1z), az)
      in
        |>: goalM #> (H, axiom)
      end

    fun True jdg =
      let
        val tr = ["Line.True"]
        val H >> AJ.TRUE ty = jdg
        val Syn.LINE (u, au) = Syn.out ty

        val v = Sym.new ()
        val av = substVar (VarKit.toDim v, u) au
        val (mainGoal, mhole) = makeTrue tr (H @> (v, AJ.TERM O.DIM)) av

        val abstr = Syn.into @@ Syn.ABS (v, mhole)
      in
        |>: mainGoal #> (H, abstr)
      end

    fun Eta jdg =
      let
        val tr = ["Line.Eta"]
        val H >> ajdg = jdg
        val ((m, n), lineTy) = View.matchTrueAsEq ajdg
        val Syn.LINE (u, _) = Syn.out lineTy

        val m' = Syn.into @@ Syn.ABS (u, Syn.into @@ Syn.DIM_APP (m, VarKit.toDim u))
        val goal1 = makeMem tr H (m, lineTy)
        val goal2 = makeEqIfDifferent tr H ((m', n), lineTy) (* m' will-typed *)
      in
        |>:? goal2 >: goal1 #> (H, axiom)
      end

    fun EqApp sign jdg =
      let
        val tr = ["Line.EqApp"]
        val H >> ajdg = jdg
        val ((ap0, ap1), ty) = View.matchAsEq ajdg
        val Syn.DIM_APP (m0, r0) = Syn.out ap0
        val Syn.DIM_APP (m1, r1) = Syn.out ap1
        val () = Assert.alphaEq (r0, r1)

        val (psi, linety) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.LINE (x, tyx) = Syn.out linety
        val tyr = substVar (r0, x) tyx
        val goalTy = View.makeAsSubType tr H (tyr, ty)
      in
        |>:+ psi >: goalTy #> (H, axiom)
      end
  end

  structure Pushout =
  struct
    val kindConstraintOnEndsAndApex =
      fn K.DISCRETE => E.raiseError @@
           E.NOT_APPLICABLE (Fpp.text "Pushouts", Fpp.text "discrete universes")
       | K.KAN => (K.COE, K.COE)
       | K.COE => (K.COE, K.COE)
       | K.HCOM => (K.PRE, K.PRE)
       | K.PRE => (K.PRE, K.PRE)

    fun EqType jdg =
      let
        val tr = ["Pushout.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.PUSHOUT (a0, b0, c0, (x0, f0x0), (y0, g0y0)) = Syn.out ty0
        val Syn.PUSHOUT (a1, b1, c1, (x1, f1x1), (y1, g1y1)) = Syn.out ty1
        val (kEnd, kApex) = kindConstraintOnEndsAndApex k

        val goalA = View.makeAsEqType tr H ((a0, a1), l, kEnd)
        val goalB = View.makeAsEqType tr H ((b0, b1), l, kEnd)
        val goalC = View.makeAsEqType tr H ((c0, c1), l, kApex)

        val z = Sym.new ()
        val f0z = VarKit.rename (z, x0) f0x0
        val f1z = VarKit.rename (z, x1) f1x1
        val goalF = makeEq tr (H @> (z, AJ.TRUE c0)) ((f0z, f1z), a0)
        val g0z = VarKit.rename (z, y0) g0y0
        val g1z = VarKit.rename (z, y1) g1y1
        val goalG = makeEq tr (H @> (z, AJ.TRUE c0)) ((g0z, g1z), b0)
      in
        |>: goalF >: goalG >: goalA >: goalB >: goalC #> (H, axiom)
      end

    fun EqLeft jdg =
      let
        val tr = ["Pushout.EqLeft"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.LEFT m0 = Syn.out tm0
        val Syn.LEFT m1 = Syn.out tm1

        val goalA = makeEq tr H ((m0, m1), a)

        val goalB = makeType tr H (b, K.top)
        val goalC = makeType tr H (c, K.top)
        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, x) fx, a)
        val goalG = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, y) gy, b)
      in
        |>: goalA >: goalF >: goalG >: goalB >: goalC #> (H, axiom)
      end

    fun EqRight jdg =
      let
        val tr = ["Pushout.EqRight"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.RIGHT m0 = Syn.out tm0
        val Syn.RIGHT m1 = Syn.out tm1

        val goalB = makeEq tr H ((m0, m1), b)

        val goalA = makeType tr H (a, K.top)
        val goalC = makeType tr H (c, K.top)
        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, x) fx, a)
        val goalG = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, y) gy, b)
      in
        |>: goalB >: goalF >: goalG >: goalA >: goalC #> (H, axiom)
      end

    fun EqGlue jdg =
      let
        val tr = ["Pushout.EqGlue"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.GLUE (r0, m0, fm0, gm0) = Syn.out tm0
        val Syn.GLUE (r1, m1, fm1, gm1) = Syn.out tm1
        val () = Assert.alphaEq' "Pushout.EqGlue" (r0, r1)

        val goalC = makeEq tr H ((m0, m1), c)
        val goalA = makeEq tr H ((fm0, fm1), a)
        val goalB = makeEq tr H ((gm0, gm1), b)
        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, x) fx, a)
        val goalG = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, y) gy, b)

        val goalCohF = makeEqIfDifferent tr H ((substVar (m0, x) fx, fm0), a)
        val goalCohG = makeEqIfDifferent tr H ((substVar (m0, y) gy, gm0), b)
      in
        |>: goalC >: goalA >: goalB >:? goalCohF >:? goalCohG >: goalF >: goalG #> (H, axiom)
      end

    fun EqFCom jdg =
      let
        val tr = ["Pushout.EqFCom"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.PUSHOUT (a, b, c, (x, fx), (y, gy)) = Syn.out ty
        val Syn.FCOM args0 = Syn.out tm0
        val Syn.FCOM args1 = Syn.out tm1

        val goalA = makeType tr H (a, K.top)
        val goalB = makeType tr H (b, K.top)
        val goalC = makeType tr H (c, K.top)

        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, x) fx, a)
        val goalG = makeMem tr (H @> (z, AJ.TRUE c)) (VarKit.rename (z, y) gy, b)
      in
        |>: goalF >: goalG >: goalA >: goalB >: goalC
         >:+ ComKit.genEqFComGoals tr H z (args0, args1) ty
        #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["Pushout.Elim"]
        val H >> AJ.TRUE dz = jdg
        (* pushout-rec(FCOM) steps to COM *)
        val k = K.COM
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.PUSHOUT (tyA, tyB, tyC, (x, fx), (y, gy)) = Syn.out ty

        (* We need to kind-check cz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType tr H (dz, k)

        (* left branch *)
        val a = Sym.new ()
        val atm = VarKit.toExp a
        fun dleft tm = substVar (Syn.into (Syn.LEFT tm), z) dz
        val (goalL, holeL) = makeTrue tr (H @> (a, AJ.TRUE tyA)) (dleft atm)

        (* right branch *)
        val b = Sym.new ()
        val btm = VarKit.toExp b
        fun dright tm = substVar (Syn.into (Syn.RIGHT tm), z) dz
        val (goalR, holeR) = makeTrue tr (H @> (b, AJ.TRUE tyB)) (dright btm)

        (* glue branch *)
        val v = Sym.new ()
        val vtm = VarKit.toDim v
        val c = Sym.new ()
        val ctm = VarKit.toExp c
        val fc = substVar (ctm, x) fx
        val gc = substVar (ctm, y) gy
        val glue = Syn.into @@ Syn.GLUE (vtm, ctm, fc, gc)
        val dglue = substVar (glue, z) dz
        val Hglue = H @> (v, AJ.TERM O.DIM) @> (c, AJ.TRUE tyC)
        val (goalG, holeG) = makeTrue tr Hglue dglue

        (* coherence *)
        val g0c = substVar (Syn.intoDim 0, v) holeG
        val lfc = substVar (fc, a) holeL
        val goalCohL = makeEq tr (H @> (c, AJ.TRUE tyC)) ((g0c, lfc), (dleft fc))

        val g1c = substVar (Syn.intoDim 1, v) holeG
        val rgc = substVar (gc, b) holeR
        val goalCohR = makeEq tr (H @> (c, AJ.TRUE tyC)) ((g1c, rgc), (dright gc))

        val elim = Syn.into @@ Syn.PUSHOUT_REC ((z, dz), VarKit.toExp z, ((a, holeL), (b, holeR), (v, c, holeG)))
      in
        |>: goalL >: goalR >: goalG >: goalCohL >: goalCohR >: goalKind #> (H, elim)
      end

    fun EqElim sign jdg =
      let
        val tr = ["Pushout.EqElim"]
        val H >> ajdg = jdg
        val ((elim0, elim1), ty) = View.matchAsEq ajdg
        (* pushout-rec(FCOM) steps to COM *)
        val k = K.COM
        val Syn.PUSHOUT_REC ((z0, d0z0), m0, ((a0, n0a0), (b0, p0b0), (v0, c0, q0v0c0))) = Syn.out elim0
        val Syn.PUSHOUT_REC ((z1, d1z1), m1, ((a1, n1a1), (b1, p1b1), (v1, c1, q1v1c1))) = Syn.out elim1

        (* type of eliminated term *)
        val (psi, pushoutTy) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.PUSHOUT (tyA, tyB, tyC, (xf, f), (xg, g)) = Syn.out pushoutTy

        (* motive *)
        val z = Sym.new ()
        val d0z = VarKit.rename (z, z0) d0z0
        val d1z = VarKit.rename (z, z1) d1z1
        val goalD = makeEqType tr (H @> (z, AJ.TRUE pushoutTy)) ((d0z, d1z), k)

        (* result type*)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (substVar (m0, z0) d0z0, ty)

        (* left branch *)
        val a = Sym.new ()
        val atm = VarKit.toExp a
        val n0a = VarKit.rename (a, a0) n0a0
        val n1a = VarKit.rename (a, a1) n1a1
        fun dleft tm = substVar (Syn.into (Syn.LEFT tm), z0) d0z0
        val goalN = makeEq tr (H @> (a, AJ.TRUE tyA)) ((n0a, n1a), (dleft atm))

        (* right branch *)
        val b = Sym.new ()
        val btm = VarKit.toExp b
        val p0b = VarKit.rename (b, b0) p0b0
        val p1b = VarKit.rename (b, b1) p1b1
        fun dright tm = substVar (Syn.into (Syn.RIGHT tm), z0) d0z0
        val goalP = makeEq tr (H @> (b, AJ.TRUE tyB)) ((p0b, p1b), (dright btm))

        (* glue branch *)
        val v = Sym.new ()
        val vtm = VarKit.toDim v
        val c = Sym.new ()
        val ctm = VarKit.toExp c
        val q0vc = VarKit.renameMany [(v, v0), (c, c0)] q0v0c0
        val q1vc = VarKit.renameMany [(v, v1), (c, c1)] q1v1c1

        val fc = substVar (ctm, xf) f
        val gc = substVar (ctm, xg) g

        val glue = Syn.into @@ Syn.GLUE (vtm, ctm, fc, gc)
        val dglue = substVar (glue, z0) d0z0
        val Hglue = H @> (v, AJ.TERM O.DIM) @> (c, AJ.TRUE tyC)
        val goalQ = makeEq tr Hglue ((q0vc, q1vc), dglue)

        (* coherence *)
        val q00c = substVar (Syn.intoDim 0, v) q0vc
        val lfc = substVar (fc, a0) n0a0
        val goalCohL = makeEq tr (H @> (c, AJ.TRUE tyC)) ((q00c, lfc), (dleft fc))

        val q01c = substVar (Syn.intoDim 1, v) q0vc
        val rgc = substVar (gc, b0) p0b0
        val goalCohR = makeEq tr (H @> (c, AJ.TRUE tyC)) ((q01c, rgc), (dright gc))
      in
        |>: goalN >: goalP >: goalQ >: goalCohL >: goalCohR >: goalD >:+ psi >:? goalTy #> (H, axiom)
      end

    fun BetaGlue jdg =
      let
        val tr = ["Pushout.BetaGlue"]
        val H >> ajdg = jdg
        val ((elim, s), ty) = View.matchAsEq ajdg
        val Syn.PUSHOUT_REC (_, m, ((a, na), (b, pb), (v, c, qvc))) = Syn.out elim
        val Syn.GLUE (r, t, ft, gt) = Syn.out m

        (* reduced goal *)
        val qrt = VarKit.substMany [(r, v),(t, c)] qvc
        val goalRed = View.makeAsEq tr H ((qrt, s), ty)

        (* left coherence *)
        val q0t = VarKit.substMany [(Syn.intoDim 0, v), (t, c)] qvc
        val nft = substVar (ft, a) na
        val goalCohL = Restriction.View.makeAsEqIfAllDifferent tr [(r, Syn.intoDim 0)] H ((nft, s), ty) [q0t]

        (* right coherence *)
        val q1t = VarKit.substMany [(Syn.intoDim 1, v), (t, c)] qvc
        val pgt = substVar (gt, b) pb
        val goalCohR = Restriction.View.makeAsEqIfAllDifferent tr [(r, Syn.intoDim 1)] H ((pgt, s), ty) [q1t]
      in
        |>: goalRed >:? goalCohL >:? goalCohR #> (H, axiom)
      end
  end

  structure Coequalizer =
  struct
    val kindConstraintOnCodAndDom =
      fn K.DISCRETE => E.raiseError @@
           E.NOT_APPLICABLE (Fpp.text "Coequalizers", Fpp.text "discrete universes")
       | K.KAN => (K.COE, K.COE)
       | K.COE => (K.COE, K.COE)
       | K.HCOM => (K.PRE, K.PRE)
       | K.PRE => (K.PRE, K.PRE)

    fun EqType jdg =
      let
        val tr = ["Coequalizer.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.COEQUALIZER (a0, b0, (x0, f0x0), (y0, g0y0)) = Syn.out ty0
        val Syn.COEQUALIZER (a1, b1, (x1, f1x1), (y1, g1y1)) = Syn.out ty1
        val (kCod, kDom) = kindConstraintOnCodAndDom k

        val goalA = View.makeAsEqType tr H ((a0, a1), l, kDom)
        val goalB = View.makeAsEqType tr H ((b0, b1), l, kCod)

        val z = Sym.new ()
        val f0z = VarKit.rename (z, x0) f0x0
        val f1z = VarKit.rename (z, x1) f1x1
        val goalF = makeEq tr (H @> (z, AJ.TRUE a0)) ((f0z, f1z), b0)
        val g0z = VarKit.rename (z, y0) g0y0
        val g1z = VarKit.rename (z, y1) g1y1
        val goalG = makeEq tr (H @> (z, AJ.TRUE a0)) ((g0z, g1z), b0)
      in
        |>: goalF >: goalG >: goalA >: goalB #> (H, axiom)
      end

    fun EqCod jdg =
      let
        val tr = ["Coequalizer.EqCod"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.COEQUALIZER (a, b, (x, fx), (y, gy)) = Syn.out ty
        val Syn.CECOD m0 = Syn.out tm0
        val Syn.CECOD m1 = Syn.out tm1

        val goalB = makeEq tr H ((m0, m1), b)

        val goalA = makeType tr H (a, K.top)
        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE a)) (VarKit.rename (z, x) fx, b)
        val goalG = makeMem tr (H @> (z, AJ.TRUE a)) (VarKit.rename (z, y) gy, b)
      in
        |>: goalB >: goalF >: goalG >: goalA #> (H, axiom)
      end

    fun EqDom jdg =
      let
        val tr = ["Pushout.EqDom"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.COEQUALIZER (a, b, (x, fx), (y, gy)) = Syn.out ty
        val Syn.CEDOM (r0, m0, fm0, gm0) = Syn.out tm0
        val Syn.CEDOM (r1, m1, fm1, gm1) = Syn.out tm1
        val () = Assert.alphaEq' "Pushout.EqDom" (r0, r1)

        val goalA = makeEq tr H ((m0, m1), a)
        val goalFM = makeEq tr H ((fm0, fm1), b)
        val goalGM = makeEq tr H ((gm0, gm1), b)
        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE a)) (VarKit.rename (z, x) fx, b)
        val goalG = makeMem tr (H @> (z, AJ.TRUE a)) (VarKit.rename (z, y) gy, b)

        val goalCohF = makeEqIfDifferent tr H ((substVar (m0, x) fx, fm0), b)
        val goalCohG = makeEqIfDifferent tr H ((substVar (m0, y) gy, gm0), b)
      in
        |>: goalA >: goalFM >: goalGM >:? goalCohF >:? goalCohG >: goalF >: goalG #> (H, axiom)
      end

    fun EqFCom jdg =
      let
        val tr = ["Coequalizer.EqFCom"]
        val H >> ajdg = jdg
        val ((tm0, tm1), ty) = View.matchTrueAsEq ajdg
        val Syn.COEQUALIZER (a, b, (x, fx), (y, gy)) = Syn.out ty
        val Syn.FCOM args0 = Syn.out tm0
        val Syn.FCOM args1 = Syn.out tm1

        val goalA = makeType tr H (a, K.top)
        val goalB = makeType tr H (b, K.top)

        val z = Sym.new ()
        val goalF = makeMem tr (H @> (z, AJ.TRUE a)) (VarKit.rename (z, x) fx, b)
        val goalG = makeMem tr (H @> (z, AJ.TRUE a)) (VarKit.rename (z, y) gy, b)
      in
        |>: goalF >: goalG >: goalA >: goalB
         >:+ ComKit.genEqFComGoals tr H z (args0, args1) ty
        #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["Coequalizer.Elim"]
        val H >> AJ.TRUE pz = jdg
        (* coeq-rec(FCOM) steps to COM *)
        val k = K.COM
        val AJ.TRUE ty = Hyps.lookup H z
        val Syn.COEQUALIZER (tyA, tyB, (x, fx), (y, gy)) = Syn.out ty

        (* We need to kind-check pz because of FCOM
         * This goal is made (explicitly) unconditional to simplify tactic writing
         *)
        val goalKind = makeType tr H (pz, k)

        (* codomain branch *)
        val b = Sym.new ()
        val btm = VarKit.toExp b
        fun pcod tm = substVar (Syn.into (Syn.CECOD tm), z) pz
        val (goalC, holeC) = makeTrue tr (H @> (b, AJ.TRUE tyB)) (pcod btm)

        (* domain branch *)
        val v = Sym.new ()
        val vtm = VarKit.toDim v
        val a = Sym.new ()
        val atm = VarKit.toExp a
        val fa = substVar (atm, x) fx
        val ga = substVar (atm, y) gy
        val dom = Syn.into @@ Syn.CEDOM (vtm, atm, fa, ga)
        val pdom = substVar (dom, z) pz
        val Hdom = H @> (v, AJ.TERM O.DIM) @> (a, AJ.TRUE tyA)
        val (goalD, holeD) = makeTrue tr Hdom pdom

        (* coherence *)
        val d0a = substVar (Syn.intoDim 0, v) holeD
        val cfa = substVar (fa, b) holeC
        val goalCohF = makeEq tr (H @> (a, AJ.TRUE tyA)) ((d0a, cfa), (pcod fa))

        val d1a = substVar (Syn.intoDim 1, v) holeD
        val cga = substVar (ga, b) holeC
        val goalCohG = makeEq tr (H @> (a, AJ.TRUE tyA)) ((d1a, cga), (pcod ga))

        val elim = Syn.into @@ Syn.COEQUALIZER_REC ((z, pz), VarKit.toExp z, ((b, holeC), (v, a, holeD)))
      in
        |>: goalC >: goalD >: goalCohF >: goalCohG >: goalKind #> (H, elim)
      end

    fun EqElim sign jdg =
      let
        val tr = ["Coequalizer.EqElim"]
        val H >> ajdg = jdg
        val ((elim0, elim1), ty) = View.matchAsEq ajdg
        (* coeq-rec(FCOM) steps to COM *)
        val k = K.COM
        val Syn.COEQUALIZER_REC ((z0, p0z0), m0, ((b0, n0b0), (v0, a0, q0v0a0))) = Syn.out elim0
        val Syn.COEQUALIZER_REC ((z1, p1z1), m1, ((b1, n1b1), (v1, a1, q1v1a1))) = Syn.out elim1

        (* type of eliminated term *)
        val (psi, tyCoeq) = Synth.synthTerm sign tr H (m0, m1)
        val Syn.COEQUALIZER (tyA, tyB, (xf, f), (xg, g)) = Syn.out tyCoeq

        (* motive *)
        val z = Sym.new ()
        val p0z = VarKit.rename (z, z0) p0z0
        val p1z = VarKit.rename (z, z1) p1z1
        val goalP = makeEqType tr (H @> (z, AJ.TRUE tyCoeq)) ((p0z, p1z), k)

        (* result type*)
        val goalTy = View.makeAsSubTypeIfDifferent tr H (substVar (m0, z0) p0z0, ty)

        (* codomain branch *)
        val b = Sym.new ()
        val btm = VarKit.toExp b
        val n0b = VarKit.rename (b, b0) n0b0
        val n1b = VarKit.rename (b, b1) n1b1
        fun pcod tm = substVar (Syn.into (Syn.CECOD tm), z0) p0z0
        val goalN = makeEq tr (H @> (b, AJ.TRUE tyB)) ((n0b, n1b), (pcod btm))

        (* glue branch *)
        val v = Sym.new ()
        val vtm = VarKit.toDim v
        val a = Sym.new ()
        val atm = VarKit.toExp a
        val q0va = VarKit.renameMany [(v, v0), (a, a0)] q0v0a0
        val q1va = VarKit.renameMany [(v, v1), (a, a1)] q1v1a1

        val fa = substVar (atm, xf) f
        val ga = substVar (atm, xg) g

        val dom = Syn.into @@ Syn.CEDOM (vtm, atm, fa, ga)
        val pdom = substVar (dom, z0) p0z0
        val Hdom = H @> (v, AJ.TERM O.DIM) @> (a, AJ.TRUE tyA)
        val goalQ = makeEq tr Hdom ((q0va, q1va), pdom)

        (* coherence *)
        val q00a = substVar (Syn.intoDim 0, v) q0va
        val cfa = substVar (fa, b0) n0b0
        val goalCohF = makeEq tr (H @> (a, AJ.TRUE tyA)) ((q00a, cfa), (pcod fa))

        val q01a = substVar (Syn.intoDim 1, v) q0va
        val cga = substVar (ga, b0) n0b0
        val goalCohG = makeEq tr (H @> (a, AJ.TRUE tyA)) ((q01a, cga), (pcod ga))
      in
        |>: goalN >: goalQ >: goalCohF >: goalCohG >: goalP >:+ psi >:? goalTy #> (H, axiom)
      end


    fun BetaDom jdg =
      let
        val tr = ["Coequalizer.BetaDom"]
        val H >> ajdg = jdg
        val ((elim, s), ty) = View.matchAsEq ajdg
      
        val Syn.COEQUALIZER_REC (_, m, ((b, nb), (v, a, qva))) = Syn.out elim
        val Syn.CEDOM (r, t, ft, gt) = Syn.out m

        val qrt = VarKit.substMany [(r, v), (t, a)] qva
        val goalRed = View.makeAsEq tr H ((qrt, s), ty)

        (* left coherence *)
        val q0t = VarKit.substMany [(Syn.intoDim 0, v), (t, a)] qva
        val nft = substVar (ft, b) nb
        val goalCohL = Restriction.View.makeAsEqIfAllDifferent tr [(r, Syn.intoDim 0)] H ((nft, s), ty) [q0t]

        (* right coherence *)
        val q1t = VarKit.substMany [(Syn.intoDim 1, v), (t, a)] qva
        val ngt = substVar (gt, b) nb
        val goalCohR = Restriction.View.makeAsEqIfAllDifferent tr [(r, Syn.intoDim 1)] H ((ngt, s), ty) [q1t]
      in
        |>: goalRed >:? goalCohL >:? goalCohR #> (H, axiom)
      end
  end

  structure InternalizedEquality =
  struct
    val kindConstraintOnBase =
      fn K.DISCRETE => K.DISCRETE
       | K.KAN => K.DISCRETE
       | K.HCOM => K.PRE
       | K.COE => K.DISCRETE
       | K.PRE => K.PRE

    fun EqType jdg =
      let
        val tr = ["InternalizedEquality.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.EQUALITY (a0, m0, n0) = Syn.out ty0
        val Syn.EQUALITY (a1, m1, n1) = Syn.out ty1
        val ka = kindConstraintOnBase k

        val goalTy = View.makeAsEqType tr H ((a0, a1), l, ka)
        val goalM = makeEq tr H ((m0, m1), a0)
        val goalN = makeEq tr H ((n0, n1), a0)
      in
        |>: goalM >: goalN >: goalTy #> (H, axiom)
      end

    fun Eq jdg =
      let
        val tr = ["InternalizedEquality.Eq"]
        val H >> ajdg = jdg
        val ((ax0, ax1), ty) = View.matchTrueAsEq ajdg
        val Syn.EQUALITY (a, m, n) = Syn.out ty
        val Syn.AX = Syn.out ax0
        val Syn.AX = Syn.out ax1

        val goal = makeEq tr H ((m, n), a)
      in
        |>: goal #> (H, axiom)
      end

    fun Eta jdg =
      let
        val tr = ["InternalizedEquality.Eta"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.EQUALITY _ = Syn.out ty

        val goal1 = makeMem tr H (m, ty)
        val goal2 = makeEqIfDifferent tr H ((Syn.into Syn.AX, n), ty)
      in
        |>:? goal2 >: goal1 #> (H, axiom)
      end

    fun Elim z jdg =
      let
        val tr = ["InternalizedEquality.Elim"]
        val H >> ajdg = jdg
        val ((m, n), a) = View.matchTrueAsEq (Hyps.lookup H z)

        val (goal, hole) =
          makeGoal tr
            @@ Hyps.substAfter (z, axiom) H
            >> AJ.map (substVar (axiom, z)) ajdg
      in
        |>: goal #> (H, hole)
      end

    (* (= ty m n) at l >> m/n = m/n in ty at l *)
    (* this is for non-deterministic search *)
    fun NondetEqFromTrueEq z jdg =
      let
        val tr = ["InternalizedEquality.NondetEqFromTrueEq"]
        val H >> ajdg = jdg
        val ((m1, n1), ty1) = View.matchTrueAsEq ajdg
        val ((m0, n0), ty0) = View.matchTrueAsEq (Hyps.lookup H z)
        val _ = Assert.alphaEqEither ((m0, n0), m1)
        val _ = Assert.alphaEqEither ((m0, n0), n1)
        val _ = Assert.alphaEq (ty0, ty1)
      in
        T.empty #> (H, axiom)
      end

    (* (= ty m n) >> ty = ty at l *)
    (* this is for non-deterministic search *)
    fun NondetTypeFromTrueEqAtType z jdg =
      let
        val tr = ["InternalizedEquality.NondetTypeFromTrueEqAtType"]
        val H >> AJ.EQ_TYPE ((ty0, ty1), k) = jdg
        val (_, ty') = View.matchTrueAsEq (Hyps.lookup H z)
        val _ = Assert.alphaEq (ty0, ty1)
        val _ = Assert.alphaEq (ty', ty0)
        val _ = Assert.kindLeq (K.top, k)
      in
        T.empty #> (H, axiom)
      end

    fun Rewrite sign (sel, acc) eqterm jdg =
      let
        val tr = ["InternalizedEquality.Rewrite"]
        val H >> concl = jdg

        val currentAjdg = Sequent.lookupSelector sel (H, concl)
        val allowed =
          case (currentAjdg, acc) of
             (AJ.TRUE ty, Accessor.WHOLE) => true
           | (AJ.TRUE ty, _) =>
               (case (Syn.out ty, acc) of
                   (Syn.EQUALITY _, Accessor.PART_TYPE) => true
                 | (Syn.EQUALITY _, Accessor.PART_LEFT) => true
                 | (Syn.EQUALITY _, Accessor.PART_RIGHT) => true
                 | _ => false)
           | (AJ.EQ_TYPE _, Accessor.PART_LEFT) => true
           | (AJ.EQ_TYPE _, Accessor.PART_RIGHT) => true
           | (AJ.SUB_TYPE _, Accessor.PART_LEFT) => true
           | (AJ.SUB_TYPE _, Accessor.PART_RIGHT) => true
           | (AJ.SUB_KIND _, Accessor.PART_LEFT) => true
           | _ => false
        val () = if allowed then () else
          E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "rewrite tactic",
            Fpp.hvsep [Fpp.hsep [Accessor.pretty acc, Fpp.text "of"], AJ.pretty currentAjdg])

        val currentTm = AJ.lookupAccessor acc currentAjdg
        val ty = AJ.View.classifier (currentAjdg, acc)

        val truncatedH = Sequent.truncateFrom sel H

        val (psi, eqty) = Synth.synthTerm sign tr truncatedH (eqterm, eqterm)
        val Syn.EQUALITY (dom, equandL, equandR) = Syn.out eqty

        val x = Sym.new ()
        val truncatedHx = truncatedH @> (x, AJ.TRUE dom)
        val (motiveGoal, motiveHole) = makeTerm tr truncatedHx O.EXP
        val motiveWfGoal = View.makeAsMem tr truncatedHx (motiveHole, ty)

        val motiveR = substVar (equandR, x) motiveHole
        val motiveL = substVar (equandL, x) motiveHole

        val (H', concl') = Sequent.mapSelector sel (AJ.mapAccessor acc (fn _ => motiveR)) (H, concl)
        val (rewrittenGoal, rewrittenHole) = makeGoal tr @@ H' >> concl'

        val motiveMatchesMainGoal =
          case Variance.compose (Selector.variance sel, AJ.variance (currentAjdg, acc)) of
             Variance.COVAR => makeSubType tr truncatedH (motiveL, currentTm)
           | Variance.CONTRAVAR => makeSubType tr truncatedH (currentTm, motiveL)
           | Variance.ANTIVAR => View.makeAsEq tr truncatedH ((currentTm, motiveL), ty)
      in
        |>: motiveGoal >: rewrittenGoal >: motiveWfGoal >: motiveMatchesMainGoal >:+ psi
         #> (H, rewrittenHole)
      end

    (* This is a hacky up version that needs some UI-polishing. *)
    fun DepRewrite sign eqterm jdg =
      let
        val tr = ["InternalizedEquality.DepRewrite"]
        val H >> concl = jdg

        val allowed =
          case concl of
             AJ.TRUE ty =>
               (case Syn.out ty of
                   Syn.EQUALITY _ => true
                 | _ => false)
           | _ => false
        val () = if allowed then () else
          E.raiseError @@ E.NOT_APPLICABLE (Fpp.text "dependant rewrite tactic",
            AJ.pretty concl)

        val currentType = AJ.lookupAccessor Accessor.PART_TYPE concl
        val currentLeft = AJ.lookupAccessor Accessor.PART_LEFT concl
        val currentRight = AJ.lookupAccessor Accessor.PART_RIGHT concl

        val (psi, eqty) = Synth.synthTerm sign tr H (eqterm, eqterm)
        val Syn.EQUALITY (dom, equandL, equandR) = Syn.out eqty

        val x = Sym.new ()
        val Hx = H @> (x, AJ.TRUE dom)
        val (motiveTypeGoal, motiveTypeHole) = makeTerm tr Hx O.EXP
        val (motiveLeftGoal, motiveLeftHole) = makeTerm tr Hx O.EXP
        val (motiveRightGoal, motiveRightHole) = makeTerm tr Hx O.EXP
        val motiveWfGoal = makeEq tr Hx ((motiveLeftHole, motiveRightHole), motiveTypeHole)

        val motiveMatchTypeGoal = makeSubType tr H (substVar (equandL, x) motiveTypeHole, currentType)
        val motiveMatchLeftGoal = makeEq tr H ((currentLeft, substVar (equandL, x) motiveLeftHole), substVar (equandL, x) motiveTypeHole)
        val motiveMatchRightGoal = makeEq tr H ((currentRight, substVar (equandR, x) motiveRightHole), substVar (equandR, x) motiveTypeHole)
      in
        |>: motiveTypeGoal >: motiveLeftGoal >: motiveRightGoal >: motiveWfGoal
         >: motiveMatchTypeGoal
         >: motiveMatchLeftGoal
         >: motiveMatchRightGoal
         >:+ psi
         #> (H, axiom)
      end

    fun Symmetry jdg =
      let
        val tr = ["InternalizedEquality.Symmetry"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val goal = View.makeEqAsTrue tr H ((n, m), ty)
      in
        |>: goal #> (H, Syn.into Syn.AX)
      end

    fun VarFromTrue jdg =
      let
        val tr = ["Equality.VarFromTrue"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchTrueAsEq ajdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val AJ.TRUE ty' = Hyps.lookup H x
        val goalTy = makeSubTypeIfDifferent tr H (ty', ty)
      in
        |>:? goalTy #> (H, axiom)
      end
  end

  structure FormalComposition =
  struct
    val kindConstraintOnCapAndTubes =
      fn K.DISCRETE => E.raiseError @@
          E.NOT_APPLICABLE (Fpp.text "fcom types", Fpp.text "discrete universes")
       | K.KAN => (K.KAN, K.KAN)
       | K.HCOM => (K.HCOM, K.KAN) (* XXX more research needed *)
       | K.COE => (K.COM, K.KAN) (* XXX more research needed *)
       | K.PRE => (K.PRE, K.COE) (* XXX more research needed *)

    (* see the function of th same name in `ComKit` *)
    local
      fun genTubeGoals' tr H ((tubes0, tubes1), l, k) =
        ListPairUtil.mapPartialEq
          (fn ((eq, t0), (_, t1)) => Restriction.View.makeAsEqType tr [eq] H ((t0, t1), l, k))
          (tubes0, tubes1)
      fun genInterTubeGoalsExceptDiag' tr H ((tubes0, tubes1), l, k) =
        ComKit.enumInterExceptDiag
          (fn ((eq0, t0), (eq1, t1)) => Restriction.View.makeAsEqTypeIfDifferent tr [eq0, eq1] H ((t0, t1), l, k))
          (tubes0, tubes1)
    in
      fun genInterTubeGoals tr H w ((tubes0, tubes1), l, k) =
        let
          val tubes0 = ComKit.alphaRenameTubes w tubes0
          val tubes1 = ComKit.alphaRenameTubes w tubes1

          val goalsOnDiag = genTubeGoals' tr (H @> (w, AJ.TERM O.DIM)) ((tubes0, tubes1), l, k)
          val goalsNotOnDiag = genInterTubeGoalsExceptDiag' tr (H @> (w, AJ.TERM O.DIM)) ((tubes0, tubes1), l, k)
        in
          goalsOnDiag @ goalsNotOnDiag
        end
    end

    (* see the function of th same name in `ComKit` *)
    fun genCapTubeGoalsIfDifferent tr H ((cap, (r, tubes)), l, k) =
      List.mapPartial
        (fn (eq, (u, tube)) =>
          Restriction.View.makeAsEqTypeIfDifferent tr [eq] H ((cap, substVar (r, u) tube), l, k))
        tubes

    fun genBoundaryGoals tr H ((boundaries0, boundaries1), tubes) =
      ListPairUtil.mapPartialEq
        (fn (((eq, b0), t), (_, b1)) => Restriction.makeEq tr [eq] H ((b0, b1), t))
        (ListPair.zipEq (boundaries0, tubes), boundaries1)

    fun genInterBoundaryGoalsExceptDiag tr H ((boundaries0, boundaries1), tubes) =
      ComKit.enumInterExceptDiag
        (fn (((eq0, b0), t), (eq1, b1)) => Restriction.makeEqIfDifferent tr [eq0, eq1] H ((b0, b1), t))
        (ListPair.zipEq (boundaries0, tubes), boundaries1)

    fun genInterBoundaryGoals tr H ((boundaries0, boundaries1), tubes) =
      genBoundaryGoals tr H ((boundaries0, boundaries1), tubes)
        @ genInterBoundaryGoalsExceptDiag tr H ((boundaries0, boundaries1), tubes)

    fun genCapBoundaryGoals tr H ((cap, ((r, r'), tyTubes, boundaries)), tyCap) =
      ListPairUtil.mapPartialEq
        (fn ((eq, ty), boundary) =>
          Restriction.makeEqIfDifferent tr [eq] H
            ((cap, Syn.into (Syn.COE {dir=(r', r), ty=ty, coercee=boundary})), tyCap))
        (tyTubes, boundaries)

    fun EqType jdg =
      let
        val tr = ["FormalComposition.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.FCOM {dir=dir0, cap=cap0, tubes=tubes0} = Syn.out ty0
        val Syn.FCOM {dir=dir1, cap=cap1, tubes=tubes1} = Syn.out ty1
        val () = Assert.dirEq "FormalComposition.EqType direction" (dir0, dir1)
        val eqs0 = List.map #1 tubes0
        val eqs1 = List.map #1 tubes1
        val _ = Assert.equationsEq "FormalComposition.EqType equations" (eqs0, eqs1)
        val _ = Assert.tautologicalEquations "FormalComposition.EqType tautology checking" eqs0

        val (kCap, kTube) = kindConstraintOnCapAndTubes k

        val goalCap = View.makeAsEqType tr H ((cap0, cap1), l, kCap)

        val w = Sym.new ()
      in
        |>: goalCap
         >:+ genInterTubeGoals tr H w ((tubes0, tubes1), l, kTube)
         >:+ genCapTubeGoalsIfDifferent tr H ((cap0, (#1 dir0, tubes0)), l, kCap) (* kCap is less demanding *)
        #> (H, axiom)
      end

    fun Eq jdg =
      let
        val tr = ["FormalComposition.Eq"]
        val H >> ajdg = jdg
        val ((box0, box1), ty) = View.matchTrueAsEq ajdg
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

        val (kCap, kTube) = kindConstraintOnCapAndTubes K.top

        val goalCap = makeEq tr H ((cap0, cap1), tyCap)

        val tyBoundaries = List.map (fn (u, ty) => substVar (#2 dir, u) ty) tyTubes'

        val w = Sym.new ()
      in
        |>: goalCap
         >:+ genInterBoundaryGoals tr H ((boundaries0, boundaries1), tyBoundaries)
         >:+ genCapBoundaryGoals tr H ((cap0, (dir, tyTubes, boundaries')), tyCap)
         >:+ genInterTubeGoals tr H w ((tyTubes, tyTubes), View.OMEGA, kTube)
         >:+ genCapTubeGoalsIfDifferent tr H ((tyCap, (#1 dir, tyTubes)), View.OMEGA, kCap)
        #> (H, axiom)
      end

    fun True jdg =
      let
        val tr = ["FormalComposition.True"]
        val H >> AJ.TRUE ty = jdg
        val Syn.FCOM {dir, cap=tyCap, tubes=tyTubes} = Syn.out ty
        val (eqs, tyTubes') = ListPair.unzip tyTubes
        val _ = Assert.tautologicalEquations "FormalComposition.True tautology checking" eqs

        val (kCap, kTube) = kindConstraintOnCapAndTubes K.top

        val (goalCap, holeCap) = makeTrue tr H tyCap

        fun goTube (eq, (u, tyTube)) =
          Restriction.makeTrue tr [eq] (Syn.into Syn.AX) H (substVar (#2 dir, u) tyTube)
        val goalHoleBoundaries = List.map goTube tyTubes
        val goalBoundaries = List.mapPartial #1 goalHoleBoundaries
        val holeBoundaries = List.map #2 goalHoleBoundaries

        val tyBoundaries = List.map (fn (u, ty) => substVar (#2 dir, u) ty) tyTubes'
        val holeBoundaries' = ListPair.zipEq (eqs, holeBoundaries)

        val w = Sym.new ()

        val box = Syn.into @@ Syn.BOX {dir=dir, cap=holeCap, boundaries=holeBoundaries'}
      in
        |>: goalCap
         >:+ goalBoundaries
         >:+ genInterBoundaryGoalsExceptDiag tr H ((holeBoundaries', holeBoundaries'), tyBoundaries)
         >:+ genCapBoundaryGoals tr H ((holeCap, (dir, tyTubes, holeBoundaries)), tyCap)
         >:+ genInterTubeGoals tr H w ((tyTubes, tyTubes), View.OMEGA, kTube)
         >:+ genCapTubeGoalsIfDifferent tr H ((tyCap, (#1 dir, tyTubes)), View.OMEGA, kCap)
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
       | K.PRE => (K.PRE, K.PRE)

    fun intoHasAllPathsTo C c =
      let
        val c' = Sym.new ()
        val dummy = Sym.new ()
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

    fun EqType jdg =
      let
        val tr = ["V.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.V (r0, a0, b0, e0) = Syn.out ty0
        val Syn.V (r1, a1, b1, e1) = Syn.out ty1
        val () = Assert.alphaEq' "V.EqType" (r0, r1)
        val (kA, kB) = kindConstraintOnEnds k

        val eq = (r0, Syn.into Syn.DIM0)

        val goalA = Restriction.View.makeAsEqType tr [eq] H ((a0, a1), l, kA)
        val goalB = View.makeAsEqType tr H ((b0, b1), l, kB)
        val goalEquiv = Restriction.makeEq tr [eq] H ((e0, e1), intoEquiv a0 b0)
      in
        |>:? goalEquiv >:? goalA >: goalB #> (H, axiom)
      end

    fun Eq jdg =
      let
        val tr = ["V.Eq"]
        val H >> ajdg = jdg
        val ((in0, in1), ty) = View.matchTrueAsEq ajdg
        val Syn.V (r, a, b, e) = Syn.out ty
        val Syn.VIN (r0, m0, n0) = Syn.out in0
        val Syn.VIN (r1, m1, n1) = Syn.out in1
        val () = Assert.alphaEq' "V.Eq" (r0, r1)
        val () = Assert.alphaEq' "V.Eq" (r0, r)

        val eq = (r0, Syn.into Syn.DIM0)

        val goalM = Restriction.makeEq tr [eq] H ((m0, m1), a)
        val goalN = makeEq tr H ((n0, n1), b)
        val goalCoh = Restriction.makeEqIfDifferent tr [eq] H
          ((Syn.intoApp (Syn.into @@ Syn.PROJ (O.indexToLabel 0, e), m0), n0), b)
        val goalEquiv = Restriction.makeMem tr [eq] H (e, intoEquiv a b)
      in
        |>:? goalM >: goalN >:? goalCoh >:? goalEquiv #> (H, axiom)
      end

    fun True jdg =
      let
        val tr = ["V.True"]
        val H >> AJ.TRUE ty = jdg
        val Syn.V (r, a, b, e) = Syn.out ty

        val eq = (r, Syn.into Syn.DIM0)

        val (goalM, holeM) = Restriction.makeTrue tr [eq] (Syn.into Syn.AX) H a
        val (goalN, holeN) = makeTrue tr H b
        val goalCoh = Restriction.makeEq tr [eq] H
          ((Syn.intoApp (Syn.into @@ Syn.PROJ (O.indexToLabel 0, e), holeM), holeN), b)
        val goalEquiv = Restriction.makeMem tr [eq] H (e, intoEquiv a b)
      in
        |>:? goalM >: goalN >:? goalCoh >:? goalEquiv
        #> (H, Syn.into @@ Syn.VIN (r, holeM, holeN))
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
       | K.PRE => K.COE

    val inherentLevel = L.succ

    fun EqType jdg =
      let
        val tr = ["Universe.EqType"]
        val H >> ajdg = jdg
        val ((ty0, ty1), l, k) = View.matchAsEqType ajdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty0
        val Syn.UNIVERSE (l1, k1) = Syn.out ty1
        val _ = Assert.levelEq (l0, l1)
        val _ = Assert.kindEq (k0, k1)
        val _ = View.Assert.univMem ((l0, k0), (l, k))
      in
        T.empty #> (H, axiom)
      end

    fun SubType jdg =
      let
        val tr = ["Universe.SubType"]
        val H >> AJ.SUB_TYPE (ty0, ty1) = jdg
        val Syn.UNIVERSE (l0, k0) = Syn.out ty0
        val Syn.UNIVERSE (l1, k1) = Syn.out ty1
        val _ = Assert.levelLeq (l0, l1)
        val _ = Assert.kindLeq (k0, k1)
      in
        T.empty #> (H, axiom)
      end

    fun SubKind jdg =
      let
        val tr = ["Universe.SubKind"]
        val H >> AJ.SUB_KIND (univ, k) = jdg
        val Syn.UNIVERSE (_, k0) = Syn.out univ
        val _ = Assert.kindLeq (k0, k)
      in
        T.empty #> (H, axiom)
      end

    (* (= (U l k) ty0 ty1) >> ty0 = ty1 with k *)
    (* this is for non-deterministic search *)
    fun NondetEqTypeFromTrueEqType z jdg =
      let
        val tr = ["Universe.NondetEqTypeFromEq"]
        val H >> AJ.EQ_TYPE ((ty0, ty1), k) = jdg
        val ((ty0', ty1'), univ) = View.matchTrueAsEq (Hyps.lookup H z)
        val Syn.UNIVERSE (_, k') = Syn.out univ
        val _ = Assert.alphaEqEither ((ty0', ty1'), ty0)
        val _ = Assert.alphaEqEither ((ty0', ty1'), ty1)
        val _ = Assert.kindLeq (k', k)
      in
        T.empty #> (H, axiom)
      end

    fun VarFromTrue jdg =
      let
        val tr = ["Universe.VarFromTrue"]
        val H >> AJ.EQ_TYPE ((ty1, ty2), k1) = jdg
        val Syn.VAR (x1, _) = Syn.out ty1
        val Syn.VAR (x2, _) = Syn.out ty2
        val _ = Assert.varEq (x1, x2)
        val AJ.TRUE univ0 = Hyps.lookup H x1
        val Syn.UNIVERSE (_, k0) = Syn.out univ0

        val goal = makeTypeUnlessSubUniv tr H (ty1, k1) k0
      in
        |>:? goal #> (H, axiom)
      end
  end
end
