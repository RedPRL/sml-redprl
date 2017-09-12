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
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, l, k)) = jdg
        val k = K.meet (k, K.COE)
        val Syn.COE {dir=dir0, ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=dir1, ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = Assert.dirEq "Coe.Eq direction" (dir0, dir1)

        (* type *)
        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u) ty0u
        val ty1w = substSymbol (P.ret w, v) ty1v
        val goalTy = makeEqType (I @ [(w, P.DIM)], H) ((ty0w, ty1w), l, k)
        (* after proving the above goal, [ty0r'0] must be a type *)
        val ty0r'0 = substSymbol (#2 dir0, u) ty0u
        val goalTy0 = makeSubType (I, H) (ty0r'0, l, k) (ty, l, k)

        (* coercee *)
        val ty0r0 = substSymbol (#1 dir0, u) ty0u
        val goalCoercees = makeEq (I, H) ((m0, m1), (ty0r0, NONE, K.top))
      in
        |>: goalCoercees >:? goalTy0 >: goalTy #> (I, H, trivial)
      end

    fun EqCapL _ jdg =
      let
        val _ = RedPrlLog.trace "Coe.EqCapL"
        val (I, H) >> CJ.EQ ((coe, other), (ty, l, k)) = jdg
        val k = K.meet (k, K.COE)
        val Syn.COE {dir=(r, r'), ty=(u, ty0u), coercee=m} = Syn.out coe
        val () = Assert.paramEq "Coe.EqCapL source and target of direction" (r, r')

        (* type *)
        val goalTy = makeType (I @ [(u, P.DIM)], H) (ty0u, l, k)
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r = substSymbol (r, u) ty0u
        val goalTy0 = makeSubType (I, H) (ty0r, l, k) (ty, l, k)

        (* eq *)
        val goalEq = makeEq (I, H) ((m, other), (ty, NONE, K.top))
      in
        |>: goalEq >:? goalTy0 >: goalTy #> (I, H, trivial)
      end
  end

  structure Computation =
  struct
    fun reduce sign =
      Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign)

    fun SequentReduce sign selectors _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.Reduce"
        val (I, H) >> catjdg = jdg
        val (H', catjdg') = Selector.map (reduce sign) selectors (H, catjdg)
        val (goal, hole) = makeGoal @@ (I, H') >> catjdg'
      in
        |>: goal #> (I, H, hole)
      end

    fun SequentReduceAll sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.ReduceAll"
        val (I, H) >> _ = jdg
        val (goal, hole) = makeGoal @@ Seq.map (reduce sign) jdg
      in
        |>: goal #> (I, H, hole)
      end

    fun MatchRecordReduce sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Computation.MatchRecordReduce"
        val MATCH_RECORD _ = jdg
        val (goal, hole) = makeGoal @@ Seq.map (reduce sign) jdg
      in
        |>: goal #> ([], Hyps.empty, hole)
      end
  end

  (* everything with custom operators *)
  structure Custom =
  struct
    local
      infix $
      fun unfoldOneTopLevel sign opid m : abt =
        case out m of
           O.POLY (O.CUST (opid',_,_)) $ _ =>
             if Sym.eq (opid, opid') then
               Machine.steps sign Machine.CUBICAL Machine.Unfolding.always 1 m
                 handle exn => E.raiseError @@ E.IMPOSSIBLE @@ Fpp.text @@ "Impossible failure during safeUnfold: " ^ exnMessage exn
             else
               m
         | _ => m
      fun unfoldOne sign opid = let val f = unfoldOneTopLevel sign opid in f o Abt.deepMapSubterms f end
    in
      fun unfold sign opids m = List.foldl (fn (opid, m) => unfoldOne sign opid m) m opids
    end

    fun UnfoldAll sign opids _ jdg =
      let
        val _ = RedPrlLog.trace "Custom.UnfoldAll"
        val (I, H) >> _ = jdg
        val (goal, hole) = makeGoal @@ Seq.map (unfold sign opids) jdg
      in
        |>: goal #> (I, H, hole)
      end

    fun Unfold sign opids selectors _ jdg =
      let
        val _ = RedPrlLog.trace "Custom.Unfold"
        val (I, H) >> catjdg = jdg
        val (H', catjdg') = Selector.map (unfold sign opids) selectors (H, catjdg)
        val (goal, hole) = makeGoal @@ (I, H') >> catjdg'
      in
        |>: goal #> (I, H, hole)
      end

    fun Eq sign _ jdg =
      let
        val _ = RedPrlLog.trace "Custom.Eq"
        val (I, H) >> CJ.EQ ((m, n), (ty, l, k)) = jdg

        val Abt.$ (O.POLY (O.CUST (name, _, _)), args) = Abt.out m
        val _ = Assert.alphaEq (m, n)

        val {spec = ([],H') >> CJ.TRUE (specTy, specL, specK), state, ...} = Sig.lookup sign name
        val Lcf.|> (psi, _) = state (fn _ => RedPrlSym.new ()) (* TODO: use alpha here??? *)
        val metas = T.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val rho =
          ListPair.foldl
            (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl)))
            Metavar.Ctx.empty (metas, args)
        val specTy' = substMetaenv rho specTy
        val _ = if Hyps.isEmpty H' then () else raise Fail "Equality.Custom only works with empty sequent"

        val goalTy = makeSubType (I, H) (specTy', specL, specK) (ty, l, k)
      in
        |>:? goalTy #> (I, H, trivial)
      end

    fun Synth sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Custom.Synth"
        val (I, H) >> CJ.SYNTH (tm, l, k) = jdg

        val Abt.$ (O.POLY (O.CUST (name, rs, _)), args) = Abt.out tm

        val {spec = (I',H') >> CJ.TRUE (ty, l', k'), state, ...} = Sig.lookup sign name
        val Lcf.|> (psi, _) = state (fn _ => RedPrlSym.new ())
        val metas = T.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val mrho =
          ListPair.foldlEq
            (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl)))
            Metavar.Ctx.empty
            (metas, args)
        val srho =
          ListPair.foldlEq
            (fn ((u, _), (r, _), rho) => Sym.Ctx.insert rho u r)
            Sym.Ctx.empty
            (I', rs)

        val ty' = substSymenv srho (substMetaenv mrho ty)
        val _ = if Hyps.isEmpty H' then () else raise Fail "Synth.Custom only works with empty sequent"

        val goalKind = makeTypeUnlessSubUniv (I, H) (ty', l, k) (l', k')
      in
        |>:? goalKind #> (I, H, ty')
      end
  end
end
