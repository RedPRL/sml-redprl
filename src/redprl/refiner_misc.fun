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

  structure MiscKit =
  struct
    fun selectiveMap f selectors (H, catjdg) =
      let
        fun folder (O.IN_GOAL, (H, catjdg)) = (H, CJ.map f catjdg)
          | folder (O.IN_HYP x, (H, catjdg)) = (Hyps.modify x (CJ.map f) H, catjdg)
      in
        List.foldl folder (H, catjdg) selectors
      end
  end

  structure Computation =
  struct
    fun reduce sign =
      Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign)

    (* favonia: the following should be generalized and put into the Sequent
     * module such that a single template function `HeadExpansionDelegate`
     * can generate all the following functions.
     *)

    open MiscKit

    fun SequentReduce sign selectors _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.Reduce"
        val (I, H) >> catjdg = jdg
        val (H', catjdg') = selectiveMap (reduce sign) selectors (H, catjdg)
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

    open MiscKit

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
        val (H', catjdg') = selectiveMap (unfold sign opids) selectors (H, catjdg)
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

        val goalTy = makeEqTypeIfDifferentOrNotSubUniv (I, H) ((ty, specTy'), l, k) (specL, specK)
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
