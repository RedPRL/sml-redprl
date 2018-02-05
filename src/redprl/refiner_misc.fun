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
        val tr = ["Coe.Eq"]
        val H >> ajdg = jdg
        val ((lhs, rhs), ty) = View.matchAsEq ajdg
        val Syn.COE {dir=dir0, ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=dir1, ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = Assert.dirEq "Coe.Eq direction" (dir0, dir1)

        (* type *)
        val w = alpha 0
        val ty0w = substVar (VarKit.toDim w, u) ty0u
        val ty1w = substVar (VarKit.toDim w, v) ty1v
        val goalTy0 = makeEqType tr (H @> (w, AJ.TERM O.DIM)) ((ty0w, ty1w), K.COE)
        (* after proving the above goal, [ty0r'0] must be a type *)
        val ty0r'0 = substVar (#2 dir0, u) ty0u
        val goalTy = View.makeAsSubTypeIfDifferent tr H (ty0r'0, ty)

        (* coercee *)
        val ty0r0 = substVar (#1 dir0, u) ty0u
        val goalCoercees = makeEq tr H ((m0, m1), ty0r0)
      in
        |>: goalCoercees >: goalTy0 >:? goalTy #> (H, axiom)
      end

    fun EqCapL _ jdg =
      let
        val tr = ["Coe.EqCapL"]
        val H >> ajdg = jdg
        val ((coe, other), ty) = View.matchAsEq ajdg
        val Syn.COE {dir=(r, r'), ty=(u, ty0u), coercee=m} = Syn.out coe
        val () = Assert.alphaEq' "Coe.EqCapL source and target of direction" (r, r')

        (* type *)
        val goalTy0 = makeType tr (H @> (u, AJ.TERM O.DIM)) (ty0u, K.COE)
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r = substVar (r, u) ty0u
        val goalTy = View.makeAsSubTypeIfDifferent tr H (ty0r, ty)

        (* eq *)
        val goalEq = View.makeAsEq tr H ((m, other), ty)
      in
        |>: goalEq >: goalTy0 >:? goalTy #> (H, axiom)
      end
  end

  structure Computation =
  struct
    fun reduce sign =
      Machine.eval sign Machine.STABLE (Machine.Unfolding.default sign)

    fun SequentReduce sign selectors _ jdg =
      let
        val tr = ["Computation.Reduce"]
        val H >> ajdg = jdg
        val (H', ajdg') = Sequent.multiMapSelector selectors (AJ.map (reduce sign)) (H, ajdg)
        val (goal, hole) = makeGoal tr @@ H' >> ajdg'
      in
        |>: goal #> (H, hole)
      end

    fun SequentReduceAll sign _ jdg =
      let
        val tr = ["Computation.ReduceAll"]
        val H >> _ = jdg
        val (goal, hole) = makeGoal tr @@ Seq.map (reduce sign) jdg
      in
        |>: goal #> (H, hole)
      end

    fun SequentReducePart sign (selector, accessors) _ jdg =
      let
        val tr = ["Computation.ReducePart"]
        val H >> ajdg = jdg
        val (H', ajdg') = Sequent.mapSelector selector (AJ.multiMapAccessor accessors (reduce sign)) (H, ajdg)
        val (goal, hole) = makeGoal tr @@ H' >> ajdg'
      in
        |>: goal #> (H, hole)
      end

    fun MatchReduce sign _ jdg =
      let
        val tr = ["Computation.MatchReduce"]
        val MATCH (th, k, a, ms) = jdg
        val (goal, hole) = makeGoal tr @@ MATCH (th, k, reduce sign a, ms)
      in
        |>: goal #> (Hyps.empty, hole)
      end

    fun MatchRecordReduce sign _ jdg = 
      let
        val tr = ["Computation.MatchRecordReduce"]
        val MATCH_RECORD (lbl, tm, tuple) = jdg
        val (goal, hole) = makeGoal tr @@ MATCH_RECORD (lbl, reduce sign tm, tuple)
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
             O.CUST (opid',_) $ _ =>
               (case List.find (fn opid => opid = opid') opids of
                   SOME _ =>
                     let
                       val m' = Machine.steps sign Machine.STABLE Machine.Unfolding.always 1 m
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
        val tr = ["Custom.UnfoldAll"]
        val H =
          case jdg of
            H >> _ => H
          | MATCH _ => Hyps.empty
          | MATCH_RECORD _ => Hyps.empty
        val (goal, hole) = makeGoal tr @@ Seq.map (unfold sign opids) jdg
      in
        |>: goal #> (H, hole)
      end

    fun Unfold sign opids selectors _ jdg =
      let
        val tr = ["Custom.Unfold"]
        val H >> ajdg = jdg
        val (H', ajdg') = Sequent.multiMapSelector selectors (AJ.map (unfold sign opids)) (H, ajdg)
        val (goal, hole) = makeGoal tr @@ H' >> ajdg'
      in
        |>: goal #> (H, hole)
      end

    fun UnfoldPart sign opids (selector, accessors) _ jdg =
      let
        val tr = ["Custom.UnfoldPart"]
        val H >> ajdg = jdg
        val (H', ajdg') = Sequent.mapSelector selector (AJ.multiMapAccessor accessors (unfold sign opids)) (H, ajdg)
        val (goal, hole) = makeGoal tr @@ H' >> ajdg'
      in
        |>: goal #> (H, hole)
      end

    fun Eq sign _ jdg =
      let
        val tr = ["Custom.Eq"]
        val H >> ajdg = jdg
        val ((m, n), ty) = View.matchAsEq ajdg

        val Abt.$ (O.CUST (name, _), args) = Abt.out m
        val _ = Assert.alphaEq (m, n)

        val AJ.TRUE specTy = Sig.theoremSpec sign name args
        val goalTy = View.makeAsSubTypeIfDifferent tr H (specTy, ty)
      in
        |>:? goalTy #> (H, axiom)
      end

  end
end
