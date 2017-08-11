(* 2017/06/24
 * As a note on programming style, the most important or most interesting
 * subgoals should go first, as long as telescopes are well-formed.
 *
 * Rules violating this principle should be updated.
 *)
functor Refiner (Sig : MINI_SIGNATURE) : REFINER =
struct
  (* This is just to get SML/NJ to typecheck the new machine module; unused code doesn't get typechecked otherwise for some reason. *)
  local structure M = RedPrlMachine (Sig) in end

  structure Kit = RefinerKit (Sig)
  structure ComRefinerKit = RefinerCompositionKit (Sig)
  structure TypeRules = RefinerTypeRules (Sig)
  open RedPrlAbt Kit ComRefinerKit TypeRules

  type sign = Sig.sign
  type rule = (int -> Sym.t) -> Lcf.jdg Lcf.tactic
  type catjdg = (Sym.t, abt) CJ.jdg
  type opid = Sig.opid
  type rule_name = string

  infixr @@
  infix 1 || #>
  infix 2 >> >: >:? >:+ $$ $# // \ @>
  infix orelse_ then_ thenl

  structure Hyp =
  struct
    fun Project z _ jdg =
      let
        val _ = RedPrlLog.trace "Hyp.Project"
        val (I, H) >> catjdg = jdg
        val catjdg' = Hyps.lookup z H
      in
        if CJ.eq (catjdg, catjdg') then
          T.empty #> (I, H, Syn.into (Syn.VAR (z, CJ.synthesis catjdg)))
        else
          raise E.error
            [Fpp.text "Hypothesis",
             Fpp.expr @@ Fpp.hsep [TermPrinter.ppSym z, Fpp.Atomic.colon, CJ.pretty' TermPrinter.ppTerm catjdg'],
             Fpp.text "does not match goal",
             CJ.pretty' TermPrinter.ppTerm catjdg]
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected sequent judgment"]

    fun Rename z alpha jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Rename"
        val (I, H) >> catjdg = jdg
        val zjdg = Hyps.lookup z H
        val z' = alpha 0

        val renameIn = VarKit.rename (z', z)
        val renameOut = VarKit.rename (z, z')

        val H' = Hyps.splice H z (Hyps.singleton z' zjdg)
        val H'' = Hyps.modifyAfter z' (CJ.map_ renameIn) H' 

        val (goal, hole) = makeGoal @@ (I, H'') >> CJ.map_ renameIn catjdg
        val extract = renameOut hole
      in
        |>: goal #> (I, H, extract)
      end

    fun Delete z _ jdg = 
      let
        val _ = RedPrlLog.trace "Hyp.Delete"
        val (I, H) >> catjdg = jdg

        fun checkCJ catjdg = 
          let
            val tm = CJ.toAbt catjdg
            val vars = varctx tm
          in
            if Var.Ctx.member vars z then 
              raise E.error [Fpp.text "Cannot delete hypothesis which is mentioned in sequent"]
            else
             ()
          end

        val _ = checkCJ catjdg
        val _ = Hyps.foldr (fn (_, catjdg, _) => (checkCJ catjdg; ())) () H

        val H' = Hyps.remove z H
        val (goal, hole) = makeGoal @@ (I, H') >> catjdg
      in
        |>: goal #> (I, H, hole)
      end
  end

  structure TypeEquality =
  struct
    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ_TYPE ((ty1, ty2), k) = jdg
        val goal = makeEqType (I, H) ((ty2, ty1), k)
      in
        |>: goal #> (I, H, trivial)
      end

    fun FromEqType z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEqType"
        val (I, H) >> CJ.EQ_TYPE ((a0, b0), k0) = jdg
        val CJ.EQ_TYPE ((a1, b1), k1) = Hyps.lookup z H
        val _ = Assert.alphaEq (a0, a1)
        val _ = Assert.alphaEq (b0, b1)
        val goal =
          case K.greatestMeetComplement' (k0, k1) of
            NONE => NONE
          | SOME k'' => SOME @@ makeEqType (I, H) ((a0, b0), k'')
      in
        |>:? goal #> (I, H, trivial)
      end

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromEq"
        val (I, H) >> CJ.EQ_TYPE ((a0, b0), k0) = jdg
        val CJ.EQ (_, (a1, k1)) = Hyps.lookup z H
        val _ = Assert.alphaEq (a0, b0)
        val _ = Assert.alphaEq (a0, a1)
        val goal =
          case K.greatestMeetComplement' (k0, k1) of
            NONE => NONE
          | SOME k'' => SOME @@ makeEqType (I, H) ((a0, b0), k'')
      in
        |>:? goal #> (I, H, trivial)
      end

    fun FromTrue z _ jdg =
      let
        val _ = RedPrlLog.trace "TypeEquality.FromTrue"
        val (I, H) >> CJ.EQ_TYPE ((a0, b0), k0) = jdg
        val CJ.TRUE (a1, k1) = Hyps.lookup z H
        val _ = Assert.alphaEq (a0, b0)
        val _ = Assert.alphaEq (a0, a1)
        val goal =
          case K.greatestMeetComplement' (k0, k1) of
            NONE => NONE
          | SOME k'' => SOME @@ makeEqType (I, H) ((a0, b0), k'')
      in
        |>:? goal #> (I, H, trivial)
      end
  end

  structure Truth =
  struct
    fun Witness tm _ jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> CJ.TRUE (ty, k) = jdg
        val goal = makeMem (I, H) (tm, (ty, k))
      in
        |>: goal #> (I, H, tm)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected truth sequent but got:", RedPrlSequent.pretty' TermPrinter.ppTerm jdg]
  end

  structure Term = 
  struct
    fun Exact tm _ jdg = 
      let
        val _ = RedPrlLog.trace "Term.Exact"
        val (I, H) >> CJ.TERM tau = jdg
        val tau' = Abt.sort tm
        val _ = Assert.sortEq (tau, tau')
      in
        T.empty #> (I, H, tm)
      end
  end

  structure Synth =
  struct
    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromEq"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg
        val CJ.EQ ((a, b), (ty, k')) = Hyps.lookup z H
        val goalKind = makeTypeIfLess (I, H) (ty, k) k'
      in
        if Abt.eq (a, tm) orelse Abt.eq (b, tm) then
          |>:? goalKind #> (I, H, ty)
        else
          raise Fail "Did not match"
      end

    fun Custom sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Synth.Custom"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg

        val Abt.$ (O.POLY (O.CUST (name, _, _)), args) = Abt.out tm

        val {spec = ([],H') >> CJ.TRUE (ty, k'), state, ...} = Sig.lookup sign name
        val Lcf.|> (psi, _) = state (fn _ => RedPrlSym.new ())
        val metas = T.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val rho =
          ListPair.foldl
            (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl)))
            Metavar.Ctx.empty (metas, args)
        val ty' = substMetaenv rho ty
        val _ = if Hyps.isEmpty H' then () else raise Fail "Synth.Custom only works with empty sequent"

        val goalKind = makeTypeIfLess (I, H) (ty', k) k'
      in
        |>:? goalKind #> (I, H, ty')
      end

    fun Hyp _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Hyp"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val CJ.TRUE (a, k') = Hyps.lookup z H
        val goalKind = makeTypeIfLess (I, H) (a, k) k'
      in
        |>:? goalKind #> (I, H, a)
      end

    fun WIf _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.If"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg
        val Syn.WIF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem (I, H) (tm, (cm, k))
      in
        |>: goal #> (I, H, cm)
      end

    fun S1Rec _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.S1Rec"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg
        val Syn.S1_REC ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem (I, H) (tm, (cm, k))
      in
        |>: goal #> (I, H, cm)
      end

    fun App _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.App"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg
        val Syn.APP (m, n) = Syn.out tm
        val (goalDFun, holeDFun) = makeSynth (I, H) (m, K.top)
        val (goalDom, holeDom) = makeMatch (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeMatch (O.MONO O.DFUN, 1, holeDFun, [], [n])
        val goalN = makeMem (I, H) (n, (holeDom, K.top))
        val goalKind = makeTypeIfLess (I, H) (holeCod, k) K.top
      in
        |>: goalDFun >: goalDom >: goalCod >: goalN >:? goalKind #> (I, H, holeCod)
      end

    fun PathApp _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.PathApp"
        val (I, H) >> CJ.SYNTH (tm, k) = jdg
        val Syn.PATH_APP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeSynth (I, H) (m, K.top)
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holePathTy, [r], [])
        val goalKind = makeTypeIfLess (I, H) (holeLine, k) K.top
      in
        |>: goalPathTy >: goalLine >:? goalKind #> (I, H, holeLine)
      end

    (* TODO: add Proj / record rule!!! *)
  end

  structure Misc =
  struct
    fun MatchOperator _ jdg =
      let
        val _ = RedPrlLog.trace "Misc.MatchOperator"
        val MATCH (th, k, tm, ps, ms) = jdg

        val Abt.$ (th', args) = Abt.out tm
        val true = Abt.O.eq Sym.eq (th, th')

        val (us, xs) \ arg = List.nth (args, k)
        val srho = ListPair.foldrEq (fn (u,p,rho) => Sym.Ctx.insert rho u p) Sym.Ctx.empty (us, ps)
        val vrho = ListPair.foldrEq (fn (x,m,rho) => Var.Ctx.insert rho x m) Var.Ctx.empty (xs, ms)

        val arg' = substEnv (srho, vrho) arg
      in
        Lcf.|> (T.empty, abtToAbs arg')
      end
      handle _ =>
        raise E.error [Fpp.text "MATCH judgment failed to unify"]

    fun ParamSubst _ jdg = 
      let
        val _ = RedPrlLog.trace "Misc.ParamSubst"
        val (I, H) >> CJ.PARAM_SUBST (psi, m, _) = jdg

        fun getSubstitution (rtm, sigma, u) = 
          case Abt.out rtm of
             Abt.$ (O.POLY (O.PARAM_REF (sigma', r)), _) =>
               if sigma = sigma' then
                 (r, u)
               else
                 raise E.error [Fpp.text "ParamSubst: parameter sort mismatch"]
           | _ => raise E.error [Fpp.text "Parameter substitution not yet materialized"]

        val substitutions = List.map getSubstitution psi
        val rho = List.foldl (fn ((r, u), rho) => Sym.Ctx.insert rho u r) Sym.Ctx.empty substitutions
      in
        T.empty #> (I, H, substSymenv rho m)
      end
  end

  structure Equality =
  struct
    fun Hyp _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Hyp"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val goalTy =
          case Hyps.lookup x H of
             CJ.TRUE (ty', k') => makeEqTypeIfDifferentOrLess (I, H) ((ty', ty), k) k'
           | _ => raise E.error [Fpp.text "Equality.Hyp: expected truth hypothesis"]
      in
        |>:? goalTy #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected variable-equality sequent"]

    fun FromEq z _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.FromEq"
        val (I, H) >> CJ.EQ ((m0, n0), (a0, k0)) = jdg
        val CJ.EQ ((m1, n1), (a1, k1)) = Hyps.lookup z H
        val _ = Assert.alphaEq (m0, m1)
        val _ = Assert.alphaEq (n0, n1)
        val _ = Assert.alphaEq (a0, a1)
        val goal =
          case K.greatestMeetComplement' (k0, k1) of
            NONE => NONE
          | SOME k'' => SOME @@ makeEq (I, H) ((m0, n0), (a0, k''))
      in
        |>:? goal #> (I, H, trivial)
      end

    fun Custom sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Equality.Custom"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg

        val Abt.$ (O.POLY (O.CUST (name, _, _)), args) = Abt.out m
        val _ = Assert.alphaEq (m, n)

        val {spec = ([],H') >> CJ.TRUE (specTy, specK), state, ...} = Sig.lookup sign name
        val Lcf.|> (psi, _) = state (fn _ => RedPrlSym.new ()) (* TODO: use alpha here??? *)
        val metas = T.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val rho =
          ListPair.foldl
            (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl)))
            Metavar.Ctx.empty (metas, args)
        val specTy' = substMetaenv rho specTy
        val _ = if Hyps.isEmpty H' then () else raise Fail "Equality.Custom only works with empty sequent"

        val goalTy = makeEqTypeIfDifferentOrLess (I, H) ((ty, specTy'), k) specK
      in
        |>:? goalTy #> (I, H, trivial)
      end

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val goal = makeEq (I, H) ((n, m), (ty, k))
      in
        |>: goal #> (I, H, trivial)
      end

    fun RewriteTrue z alpha jdg =
      let
        val _ = RedPrlLog.trace "Equality.RewriteTrue"
        val (I, H) >> CJ.TRUE (mainGoal, k) = jdg
        val CJ.EQ ((m, n), (ty, k')) = Hyps.lookup z H

        val x = alpha 0
        val Hx = H @> (x, CJ.TRUE (ty, k'))
        val (motiveGoal, motiveHole) = makeTerm (I, Hx) O.EXP

        val motiven = substVar (n, x) motiveHole
        val motivem = substVar (m, x) motiveHole

        val (rewrittenGoal, rewrittenHole) = makeTrue (I, H) (motiven, K.top)

        val motiveWfGoal = makeType (I, Hx) (motiveHole, K.top)
        val motiveMatchesMainGoal = makeEqType (I, H) ((motivem, mainGoal), k)
      in
        |>: motiveGoal >: rewrittenGoal >: motiveWfGoal >: motiveMatchesMainGoal #> (I, H, rewrittenHole)
      end
  end

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), (ty, k)) = jdg
        val k = K.meet (k, K.COE)
        val Syn.COE {dir=(r0, r'0), ty=(u, ty0u), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=(r1, r'1), ty=(v, ty1v), coercee=m1} = Syn.out rhs
        val () = Assert.paramEq "Coe.Eq source of direction" (r0, r1)
        val () = Assert.paramEq "Coe.Eq target of direction" (r'0, r'1)

        (* type *)
        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u) ty0u
        val ty1w = substSymbol (P.ret w, v) ty1v
        val goalTy = makeEqType (I @ [(w, P.DIM)], H) ((ty0w, ty1w), k)
        (* after proving the above goal, [ty0r'0] must be a type *)
        val ty0r'0 = substSymbol (r'0, u) ty0u
        val goalTy0 = makeEqTypeIfDifferent (I, H) ((ty0r'0, ty), k)

        (* coercee *)
        val ty0r0 = substSymbol (r0, u) ty0u
        val goalCoercees = makeEq (I, H) ((m0, m1), (ty0r0, K.top))
      in
        |>: goalCoercees >:? goalTy0 >: goalTy #> (I, H, trivial)
      end

    fun EqCapL _ jdg =
      let
        val _ = RedPrlLog.trace "Coe.EqCapL"
        val (I, H) >> CJ.EQ ((coe, other), (ty, k)) = jdg
        val k = K.meet (k, K.COE)
        val Syn.COE {dir=(r, r'), ty=(u, ty0u), coercee=m} = Syn.out coe
        val () = Assert.paramEq "Coe.EqCapL source and target of direction" (r, r')

        (* type *)
        val goalTy = makeType (I @ [(u, P.DIM)], H) (ty0u, k)
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r = substSymbol (r, u) ty0u
        val goalTy0 = makeEqTypeIfDifferent (I, H) ((ty0r, ty), k)

        (* eq *)
        val goalEq = makeEq (I, H) ((m, other), (ty, k))
      in
        |>: goalEq >:? goalTy0 >: goalTy #> (I, H, trivial)
      end
  end

  structure Computation =
  struct
    local
      infix $
    in
      fun safeUnfold sign opid m : abt =
        case out m of
           O.POLY (O.CUST (opid',_,_)) $ _ =>
             if Sym.eq (opid, opid') then
               Machine.steps sign Machine.CUBICAL Machine.Unfolding.always 1 m
                 handle exn => raise Fail ("Impossible failure during safeUnfold: " ^ exnMessage exn)
             else
               m
         | _ => m
    end

    fun Unfold sign opid _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.Unfold"
        val unfold = safeUnfold sign opid o Abt.deepMapSubterms (safeUnfold sign opid)
        val jdg' as (I, H) >> _ = RedPrlSequent.map unfold jdg
        val (goal, hole) = makeGoal @@ jdg'
      in
        |>: goal #> (I, H, hole)
      end

    fun EqHeadExpansion sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqHeadExpansion"
        val (I, H) >> CJ.EQ ((m, n), (ty, k)) = jdg
        val m' = Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign) m
        val goal = makeEq (I, H) ((m', n), (ty, k))
      in
        |>: goal #> (I, H, trivial)
      end
      handle _ => raise E.error [Fpp.text "EqHeadExpansion!"]

    fun EqTypeHeadExpansion sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqTypeHeadExpansion"
        val (I, H) >> CJ.EQ_TYPE ((ty1, ty2), k) = jdg
        val ty1' = Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign) ty1
        val goal = makeEqType (I, H) ((ty1', ty2), k)
      in
        |>: goal #> (I, H, trivial)
      end
    
    fun MatchRecordHeadExpansion sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Record.MatchRecord"
        val MATCH_RECORD (lbl, tm) = jdg
        val tm' = Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign) tm
        val (goal, hole) = makeMatchRecord (lbl, tm')
      in
        |>: goal #> ([], Hyps.empty, hole)
      end
  end

  fun Cut catjdg alpha jdg =
    let
      val _ = RedPrlLog.trace "Cut"
      val (I, H) >> catjdg' = jdg
      val z = alpha 0
      val (goal1, hole1) = makeGoal @@ (I, H) >> catjdg
      val (goal2, hole2) = makeGoal @@ (I, H @> (z, catjdg)) >> catjdg'
    in
      |>: goal1 >: goal2 #> (I, H, substVar (hole1, z) hole2)
    end

  fun CutLemma sign opid params alpha jdg = 
    let
      val z = alpha 0
      val (I, H) >> catjdg = jdg

      val {spec, state, ...} = Sig.lookup sign opid
      val Lcf.|> (lemmaSubgoals, _) = state @@ UniversalSpread.bite 1 alpha

      val (I_spec, H_spec) >> specjdg = spec
      val _ = 
        if Hyps.isEmpty H_spec then () else 
          raise E.error [Fpp.text "Lemmas must have a categorical judgment as a conclusion"]

      val lemmaExtract' =
        let
          val subgoalsList = T.foldr (fn (x, jdg, goals) => (x, jdg) :: goals) [] lemmaSubgoals
          val valences = List.map (RedPrlJudgment.sort o #2) subgoalsList
          val arity = (valences, CJ.synthesis specjdg)
          fun argForSubgoal ((x, jdg), vl) = outb @@ Lcf.L.var x vl
        in
          O.POLY (O.CUST (opid, params, SOME arity)) $$ ListPair.mapEq argForSubgoal (subgoalsList, valences)
        end

      val symenv = ListPair.foldlEq (fn ((x, _), r, rho) => Sym.Ctx.insert rho x r) Sym.Ctx.empty (I_spec, List.map #1 params)
      val H' = H @> (z, CJ.map_ (substSymenv symenv) specjdg)
      val (mainGoal, mainHole) = makeGoal @@ (I, H') >> catjdg
      val extract = substVar (lemmaExtract', z) mainHole
    in
      lemmaSubgoals >: mainGoal #> (I, H, extract)
    end

  fun Exact tm =
    Truth.Witness tm
      orelse_ Term.Exact tm



  val lookupRule = 
    fn "bool/eqtype" => Bool.EqType
     | "bool/eq/tt" => Bool.EqTT
     | "bool/eq/ff" => Bool.EqFF
     | "bool/eq/if" => Bool.EqElim
     | "wbool/eqtype" => WBool.EqType
     | "wbool/eq/tt" => WBool.EqTT
     | "wbool/eq/ff" => WBool.EqFF
     | "wbool/eq/fcom" => WBool.EqFCom
     | "wbool/eq/wif" => WBool.EqElim
     | "nat/eqtype" => Nat.EqType
     | "nat/eq/zero" => Nat.EqZero
     | "nat/eq/succ" => Nat.EqSucc
     | "nat/eq/nat-rec" => Nat.EqElim
     | "int/eqtype" => Int.EqType
     | "int/eq/zero" => Int.EqZero
     | "int/eq/succ" => Int.EqSucc
     | "int/eq/negsucc" => Int.EqNegSucc
     | "void/eqtype" => Void.EqType
     | "S1/eqtype" => S1.EqType
     | "S1/eq/base" => S1.EqBase
     | "S1/eq/loop" => S1.EqLoop
     | "S1/eq/fcom" => S1.EqFCom
     | "S1/eq/S1-rec" => S1.EqElim
     | "dfun/eqtype" => DFun.EqType
     | "dfun/eq/lam" => DFun.Eq
     | "dfun/intro" => DFun.True
     | "dfun/eq/eta" => DFun.Eta
     | "dfun/eq/app" => DFun.EqApp
     | "record/eqtype" => Record.EqType
     | "record/eq" => Record.Eq
     | "record/eq/eta" => Record.Eta
     | "record/eq/proj" => Record.EqProj
     | "record/intro" => Record.True
     | "path/eqtype" => Path.EqType
     | "path/eq/abs" => Path.Eq
     | "path/intro" => Path.True
     | "path/eq/eta" => Path.Eta
     | "path/eq/app" => Path.EqApp
     | "path/eq/app/const" => Path.EqAppConst
     | "eq/eqtype" => InternalizedEquality.EqType
     | "eq/eq" => InternalizedEquality.Eq
     | "eq/ax" => InternalizedEquality.True
     | "eq/eta" => InternalizedEquality.Eta
     | "hcom/eq" => HCom.Eq
     | "hcom/eq/cap" => HCom.EqCapL
     | "hcom/eq/tube" => HCom.EqTubeL

     | r => raise E.error [Fpp.text "No rule registered with name", Fpp.text r]


  local
    val CatJdgSymmetry : tactic =
      Equality.Symmetry orelse_ TypeEquality.Symmetry

    fun matchGoal f alpha jdg =
      f jdg alpha jdg
  in
    local
      fun StepEqTypeVal (ty1, ty2) =
        case (Syn.out ty1, Syn.out ty2) of
           (Syn.BOOL, Syn.BOOL) => Bool.EqType
         | (Syn.WBOOL, Syn.WBOOL) => WBool.EqType
         | (Syn.NAT, Syn.NAT) => Nat.EqType
         | (Syn.INT, Syn.INT) => Int.EqType
         | (Syn.VOID, Syn.VOID) => Void.EqType
         | (Syn.S1, Syn.S1) => S1.EqType
         | (Syn.DFUN _, Syn.DFUN _) => DFun.EqType
         | (Syn.RECORD _, Syn.RECORD _) => Record.EqType
         | (Syn.PATH_TY _, Syn.PATH_TY _) => Path.EqType
         | (Syn.EQUALITY _, Syn.EQUALITY _) => InternalizedEquality.EqType
         | _ => raise E.error [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

      fun canonicity sign = 
        Machine.canonicity sign Machine.NOMINAL (Machine.Unfolding.default sign)

      fun StepEqType sign (ty1, ty2) =
        case (canonicity sign ty1, canonicity sign ty2) of
           (Machine.REDEX, _) => Computation.EqTypeHeadExpansion sign
         | (_, Machine.REDEX) => CatJdgSymmetry then_ Computation.EqTypeHeadExpansion sign
         | (Machine.CANONICAL, Machine.CANONICAL) => StepEqTypeVal (ty1, ty2)
         | _ => raise E.error [Fpp.text "Could not find type equality rule for", TermPrinter.ppTerm ty1, Fpp.text "and", TermPrinter.ppTerm ty2]

      (* equality of canonical forms *)
      fun StepEqVal ((m, n), ty) =
        case (Syn.out m, Syn.out n, Syn.out ty) of
           (Syn.TT, Syn.TT, Syn.WBOOL) => WBool.EqTT
         | (Syn.FF, Syn.FF, Syn.WBOOL) => WBool.EqFF
         | (Syn.FCOM _, Syn.FCOM _, Syn.WBOOL) => WBool.EqFCom
         | (Syn.TT, Syn.TT, Syn.BOOL) => Bool.EqTT
         | (Syn.FF, Syn.FF, Syn.BOOL) => Bool.EqFF
         | (Syn.ZERO, Syn.ZERO, Syn.NAT) => Nat.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.NAT) => Nat.EqSucc
         | (Syn.ZERO, Syn.ZERO, Syn.INT) => Int.EqZero
         | (Syn.SUCC _, Syn.SUCC _, Syn.INT) => Int.EqSucc
         | (Syn.NEGSUCC _, Syn.NEGSUCC _, Syn.INT) => Int.EqNegSucc
         | (Syn.BASE, Syn.BASE, Syn.S1) => S1.EqBase
         | (Syn.LOOP _, Syn.LOOP _, Syn.S1) => S1.EqLoop
         | (Syn.FCOM _, Syn.FCOM _, Syn.S1) => S1.EqFCom
         | (Syn.LAM _, Syn.LAM _, _) => DFun.Eq
         | (Syn.TUPLE _, Syn.TUPLE _, _) => Record.Eq
         | (Syn.PATH_ABS _, Syn.PATH_ABS _, _) => Path.Eq
         | (Syn.AX, Syn.AX, Syn.EQUALITY _) => InternalizedEquality.Eq
         | _ => raise E.error [Fpp.text "Could not find value equality rule for", TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n, Fpp.text "at type", TermPrinter.ppTerm ty]

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeu sign (blocker1, blocker2) ((m, n), ty) =
        case (Syn.out m, blocker1, Syn.out n, blocker2) of
           (Syn.VAR _, _, Syn.VAR _, _) => Equality.Hyp
         | (Syn.IF _, _, Syn.IF _, _) => Bool.EqElim
         | (Syn.IF _, Machine.VAR z, _, _) => Bool.Elim z
         | (_, _, Syn.IF _, Machine.VAR z) => CatJdgSymmetry then_ Bool.Elim z
         | (Syn.WIF _, _, Syn.WIF _, _) => WBool.EqElim
         | (Syn.S1_REC _, _, Syn.S1_REC _, _) => S1.EqElim
         | (Syn.APP _, _, Syn.APP _, _) => DFun.EqApp
         | (Syn.PROJ _, _, Syn.PROJ _, _) => Record.EqProj
         | (Syn.PATH_APP (_, P.VAR _), _, Syn.PATH_APP (_, P.VAR _), _) => Path.EqApp
         | (Syn.CUST, _, Syn.CUST, _) => Equality.Custom sign
         | (_, Machine.OPERATOR theta, _, _) => Computation.Unfold sign theta
         | _ => raise E.error [Fpp.text "Could not find neutral equality rule for", TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n, Fpp.text "at type", TermPrinter.ppTerm ty]

      fun StepEqNeuExpand sign blocker ty =
        case (blocker, Syn.out ty) of
           (_, Syn.DFUN _) => DFun.Eta
         | (_, Syn.RECORD _) => Record.Eta
         | (_, Syn.PATH_TY _) => Path.Eta
         | (_, Syn.EQUALITY _) => InternalizedEquality.Eta
         | (Machine.OPERATOR theta, _) => Computation.Unfold sign theta
         | _ => raise E.error [Fpp.text "Could not expand neutral term of type", TermPrinter.ppTerm ty]


      structure HCom =
      struct
        open HCom

        val AutoEqL = EqCapL orelse_ EqTubeL orelse_ Eq

        (* Try all the hcom rules.
         * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
        val AutoEqLR =
          EqCapL
            orelse_ (CatJdgSymmetry then_ HCom.EqCapL)
            orelse_ HCom.EqTubeL
            orelse_ (CatJdgSymmetry then_ HCom.EqTubeL)
            orelse_ HCom.Eq
      end

      structure Coe =
      struct
       open Coe

       val EqCapR = CatJdgSymmetry then_ EqCapL
       val AutoEqLR = EqCapL orelse_ EqCapR orelse_ Eq
       val AutoEqL = EqCapL orelse_ Eq
       val AutoEqR = EqCapR orelse_ Eq
      end

      fun TryHeadExpansionL sign alpha = Lcf.try (Computation.EqHeadExpansion sign alpha)
      fun TryHeadExpansionLR sign = TryHeadExpansionL sign then_ CatJdgSymmetry then_ TryHeadExpansionL sign then_ CatJdgSymmetry

      fun StepEq sign ((m, n), ty) =
        case (Syn.out m, canonicity sign m, Syn.out n, canonicity sign n) of 
           (Syn.HCOM _, _, Syn.HCOM _, _) => HCom.AutoEqLR orelse_ TryHeadExpansionLR sign
         | (Syn.HCOM _, _, _, _) => HCom.AutoEqL orelse_ TryHeadExpansionLR sign
         | (_, _, Syn.HCOM _, _) => HCom.AutoEqLR orelse_ TryHeadExpansionLR sign
         | (Syn.COE _, _, Syn.COE _, _) => Coe.AutoEqLR orelse_ TryHeadExpansionLR sign
         | (Syn.COE _, _, _, _) => Coe.AutoEqL orelse_ TryHeadExpansionLR sign
         | (_, _, Syn.COE _, _) => Coe.AutoEqR orelse_ TryHeadExpansionLR sign
         | (_, Machine.REDEX, _, _) => Computation.EqHeadExpansion sign
         | (_, _, _, Machine.REDEX) => CatJdgSymmetry then_ Computation.EqHeadExpansion sign
         | (_, Machine.CANONICAL, _, Machine.CANONICAL) => StepEqVal ((m, n), ty)
         | (Syn.PATH_APP (_, P.APP _), _, _, _) => Path.EqAppConst
         | (_, _, Syn.PATH_APP (_, P.APP _), _) => CatJdgSymmetry then_ Path.EqAppConst
         | (_, Machine.NEUTRAL blocker1, _, Machine.NEUTRAL blocker2) => StepEqNeu sign (blocker1, blocker2) ((m, n), ty)
         | (_, Machine.NEUTRAL blocker, _, Machine.CANONICAL) => StepEqNeuExpand sign blocker ty
         | (_, Machine.CANONICAL, _, Machine.NEUTRAL blocker) => CatJdgSymmetry then_ StepEqNeuExpand sign blocker ty

      fun StepSynth sign m =
        case Syn.out m of
           Syn.VAR _ => Synth.Hyp
         | Syn.APP _ => Synth.App
         | Syn.S1_REC _ => Synth.S1Rec
         | Syn.WIF _ => Synth.WIf
         | Syn.PATH_APP _ => Synth.PathApp
         | Syn.CUST => Synth.Custom sign
         | _ => raise E.error [Fpp.text "Could not find suitable type synthesis rule for", TermPrinter.ppTerm m]

      fun StepJdg sign = matchGoal
        (fn _ >> CJ.EQ_TYPE (tys, _) => StepEqType sign tys
          | _ >> CJ.EQ ((m, n), (ty, _)) => StepEq sign ((m, n), ty)
          | _ >> CJ.SYNTH (m, _) => StepSynth sign m
          | _ >> CJ.PARAM_SUBST _ => Misc.ParamSubst
          | MATCH _ => Misc.MatchOperator
          | MATCH_RECORD _ => Record.MatchRecord orelse_ Computation.MatchRecordHeadExpansion sign then_ Record.MatchRecord
          | _ >> jdg => raise E.error [Fpp.text "AutoStep does not apply to the judgment", CJ.pretty' TermPrinter.ppTerm jdg])

      fun EqTypeFromHyp alpha jdg =
        let
          val (_, H) >> CJ.EQ_TYPE ((a0, b0), k0) = jdg
          val isUnary = Abt.eq (a0, b0)
          val isUseful =
            fn CJ.EQ_TYPE ((a1, b1), k1) =>
                 Abt.eq (a0, a1) andalso Abt.eq (b0, b1)
                 andalso K.greatestMeetComplement' (k0, k1) <> SOME k0
             | CJ.EQ (_, (a1, k1)) =>
                 isUnary andalso Abt.eq (a0, a1)
                 andalso K.greatestMeetComplement' (k0, k1) <> SOME k0
             | CJ.TRUE (a1, k1) =>
                 isUnary andalso Abt.eq (a0, a1)
                 andalso K.greatestMeetComplement' (k0, k1) <> SOME k0
             | _ => false
        in
          case Hyps.search H isUseful of
            SOME (lbl, _) =>
              ( TypeEquality.FromEqType lbl orelse_
                TypeEquality.FromEq lbl orelse_
                TypeEquality.FromTrue lbl)
              alpha jdg
          | NONE => raise E.error [Fpp.text "Could not find suitable hypothesis"]
        end

      fun EqFromHyp alpha jdg =
        let
          val (_, H) >> CJ.EQ ((m0, n0), (a0, k0)) = jdg
          val isUseful =
            fn CJ.EQ ((m1, n1), (a1, k1)) =>
                Abt.eq (m0, m1) andalso Abt.eq (n0, n1) andalso Abt.eq (a0, a1)
                andalso K.greatestMeetComplement' (k0, k1) <> SOME k0
             | _ => false
        in
          case Hyps.search H isUseful of
            SOME (lbl, _) => Equality.FromEq lbl alpha jdg
          | NONE => raise E.error [Fpp.text "Could not find suitable hypothesis"]
        end
    in
      fun AutoStep sign alpha jdg = 
        StepJdg sign alpha jdg
          handle exn => 
            (EqTypeFromHyp orelse_ EqFromHyp) alpha jdg
            handle _ => raise exn
    end

    local
      fun FromTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.WBOOL => WBool.Elim
         | Syn.NAT => Nat.Elim
         | Syn.VOID => Void.Elim
         | Syn.S1 => S1.Elim
         | Syn.DFUN _ => DFun.Elim
         | Syn.RECORD _ => Record.Elim
         | Syn.PATH_TY _ => Path.Elim
         | Syn.EQUALITY _ => InternalizedEquality.Elim
         | _ => raise E.error [Fpp.text "Could not find suitable elimination rule for", TermPrinter.ppTerm ty]

      val FromEq = Equality.RewriteTrue (* todo: rewrite other kinds of goals *)

      fun StepJdg _ z alpha jdg =
        let
          val (_, H) >> _ = jdg
        in
          case Hyps.lookup z H of
             CJ.TRUE (hyp, _) => FromTrue hyp z alpha jdg
           | CJ.EQ _ => FromEq z alpha jdg
           | _ => raise E.error [Fpp.text "Could not find suitable elimination rule"]
        end
    in
      val Elim = StepJdg
    end

  end
end
