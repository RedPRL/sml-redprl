(* other rules
 *
 * Currently there are:
 * - coe
 * - computation
 * - custom
 * *)
functor RefinerMiscRules (Sig : MINI_SIGNATURE) =
struct
  structure Kit = RefinerKit (Sig)
  open RedPrlAbt Kit
  type hyp = Sym.t
  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val H >> AJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val k = K.meet (k, K.COE)
        val Syn.COE {dir=dir0, ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=dir1, ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = Assert.dirEq "Coe.Eq direction" (dir0, dir1)

        (* type *)
        val w = alpha 0
        val ty0w = substVar (VarKit.toDim w, u) ty0u
        val ty1w = substVar (VarKit.toDim w, v) ty1v
        val goalTy = makeEqType (H @> (w, AJ.TERM O.DIM)) ((ty0w, ty1w), l, k)
        (* after proving the above goal, [ty0r'0] must be a type *)
        val ty0r'0 = substVar (#2 dir0, u) ty0u
        val goalTy0 = makeSubType H (ty0r'0, l, k) (ty, l, k)

        (* coercee *)
        val ty0r0 = substVar (#1 dir0, u) ty0u
        val goalCoercees = makeEq H ((m0, m1), (ty0r0, NONE, K.top))
      in
        |>: goalCoercees >:? goalTy0 >: goalTy #> (H, trivial)
      end

    fun EqCapL _ jdg =
      let
        val _ = RedPrlLog.trace "Coe.EqCapL"
        val H >> AJ.EQ ((coe, other), (ty, l, k)) = jdg
        val k = K.meet (k, K.COE)
        val Syn.COE {dir=(r, r'), ty=(u, ty0u), coercee=m} = Syn.out coe
        val () = Assert.alphaEq' "Coe.EqCapL source and target of direction" (r, r')

        (* type *)
        val goalTy = makeType (H @> (u, AJ.TERM O.DIM)) (ty0u, l, k)
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r = substVar (r, u) ty0u
        val goalTy0 = makeSubType H (ty0r, l, k) (ty, l, k)

        (* eq *)
        val goalEq = makeEq H ((m, other), (ty, NONE, K.top))
      in
        |>: goalEq >:? goalTy0 >: goalTy #> (H, trivial)
      end
  end

  structure Computation =
  struct
    fun reduce sign =
      Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign)

    fun SequentReduce sign selectors _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.Reduce"
        val H >> catjdg = jdg
        val (H', catjdg') = Selector.multiMap selectors (reduce sign) (H, catjdg)
        val (goal, hole) = makeGoal @@ H' >> catjdg'
      in
        |>: goal #> (H, hole)
      end

    fun SequentReduceAll sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.ReduceAll"
        val H >> _ = jdg
        val (goal, hole) = makeGoal @@ Seq.map (reduce sign) jdg
      in
        |>: goal #> (H, hole)
      end

    fun MatchRecordReduce sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Computation.MatchRecordReduce"
        val MATCH_RECORD _ = jdg
        val (goal, hole) = makeGoal @@ Seq.map (reduce sign) jdg
      in
        |>: goal #> (Hyps.empty, hole)
      end
  end

  (* everything with custom operators *)
  structure Custom =
  struct
    fun unfold sign opids m : abt =
      let
        infix $
        fun shallowUnfold m =
          case out m of
             O.POLY (O.CUST (opid',_)) $ _ =>
               (case List.find (fn opid => opid = opid') opids of
                   SOME _ =>
                     let
                       val m' = Machine.steps sign Machine.CUBICAL Machine.Unfolding.always 1 m
                         handle exn => E.raiseError @@ E.IMPOSSIBLE @@ Fpp.hvsep
                           [Fpp.text "unfolding", TermPrinter.ppTerm m, Fpp.text ":", E.format exn]
                     in
                       deepUnfold m'
                     end
                 | NONE => m)
           | _ => m
        and deepUnfold m = shallowUnfold (Abt.deepMapSubterms shallowUnfold m)
      in
        deepUnfold m
      end

    fun UnfoldAll sign opids _ jdg =
      let
        val _ = RedPrlLog.trace "Custom.UnfoldAll"
        val H >> _ = jdg
        val (goal, hole) = makeGoal @@ Seq.map (unfold sign opids) jdg
      in
        |>: goal #> (H, hole)
      end

    fun Unfold sign opids selectors _ jdg =
      let
        val _ = RedPrlLog.trace "Custom.Unfold"
        val H >> catjdg = jdg
        val (H', catjdg') = Selector.multiMap selectors (unfold sign opids) (H, catjdg)
        val (goal, hole) = makeGoal @@ H' >> catjdg'
      in
        |>: goal #> (H, hole)
      end

    fun Eq sign _ jdg =
      let
        val _ = RedPrlLog.trace "Custom.Eq"
        val H >> AJ.EQ ((m, n), (ty, l, k)) = jdg

        val Abt.$ (O.POLY (O.CUST (name, _)), args) = Abt.out m
        val _ = Assert.alphaEq (m, n)

        val {spec = H' >> AJ.TRUE (specTy, specL, specK), state, ...} = Sig.lookup sign name
        val Lcf.|> (psi, _) = state (fn _ => RedPrlSym.new ()) (* TODO: use alpha here??? *)
        val metas = T.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val rho =
          ListPair.foldl
            (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl)))
            Metavar.Ctx.empty (metas, args)
        val specTy' = substMetaenv rho specTy
        val _ = if Hyps.isEmpty H' then () else raise Fail "Equality.Custom only works with empty sequent"

        val goalTy = makeSubType H (specTy', specL, specK) (ty, l, k)
      in
        |>:? goalTy #> (H, trivial)
      end

    fun Synth sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Custom.Synth"
        val H >> AJ.SYNTH (tm, l, k) = jdg

        val Abt.$ (O.POLY (O.CUST (name, _)), args) = Abt.out tm

        val {spec = H' >> AJ.TRUE (ty, l', k'), state, ...} = Sig.lookup sign name
        val Lcf.|> (psi, _) = state (fn _ => RedPrlSym.new ())
        val metas = T.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val mrho =
          ListPair.foldlEq
            (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl)))
            Metavar.Ctx.empty
            (metas, args)


        val ty' = substMetaenv mrho ty
        val _ = if Hyps.isEmpty H' then () else raise Fail "Synth.Custom only works with empty sequent"

        val goalKind = makeTypeUnlessSubUniv H (ty', l, k) (l', k')
      in
        |>:? goalKind #> (H, ty')
      end
  end
end
