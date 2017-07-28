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
        val catjdg' = lookupHyp H z
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
        val zjdg = lookupHyp H z
        val z' = alpha 0

        val renameIn = renameVars @@ Var.Ctx.singleton z z'
        val renameOut =  renameVars @@ Var.Ctx.singleton z' z

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
      val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
      val goal = makeEqType (I, H) (ty2, ty1)
    in
      |>: goal #> (I, H, trivial)
    end
  end

  structure Truth =
  struct
    fun Witness tm _ jdg =
      let
        val _ = RedPrlLog.trace "True.Witness"
        val (I, H) >> CJ.TRUE ty = jdg
        val goal = makeMem (I, H) (tm, ty)
      in
        |>: goal #> (I, H, tm)
      end
      handle Bind =>
        raise E.error [Fpp.text @@ "Expected truth sequent but got " ^ J.toString jdg]
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
    fun FromWfHyp z _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.FromWfHyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val CJ.EQ ((a, b), ty) = lookupHyp H z
      in
        if Abt.eq (a, tm) orelse Abt.eq (b, tm) then
          T.empty #> (I, H, ty)
        else
          raise Fail "Did not match"
      end

    fun Custom sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Synth.Custom"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Abt.$ (O.POLY (O.CUST (name, _, _)), args) = Abt.out tm
        val {spec = ([],H') >> CJ.TRUE ty, state = Lcf.|> (psi, _), ...} = Sig.lookup sign name
        val metas = Lcf.Tl.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val rho = ListPair.foldl (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl))) Metavar.Ctx.empty (metas, args)
        val ty' = substMetaenv rho ty
        val _ = if Hyps.isEmpty H' then () else raise Fail "Synth.Custom only works with empty sequent"
      in
        T.empty #> (I, H, ty')
      end

    fun Hyp _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.Hyp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.VAR (z, O.EXP) = Syn.out tm
        val CJ.TRUE a = lookupHyp H z
      in
        T.empty #> (I, H, a)
      end

    fun WIf _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.If"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.WIF ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem (I, H) (tm, cm)
      in
        |>: goal #> (I, H, cm)
      end

    fun S1Rec _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.S1Rec"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.S1_REC ((x,cx), m, _) = Syn.out tm

        val cm = substVar (m, x) cx
        val goal = makeMem (I, H) (tm, cm)
      in
        |>: goal #> (I, H, cm)
      end

    fun App _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.App"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.APP (m, n) = Syn.out tm
        val (goalDFun, holeDFun) = makeSynth (I, H) m
        val (goalDom, holeDom) = makeMatch (O.MONO O.DFUN, 0, holeDFun, [], [])
        val (goalCod, holeCod) = makeMatch (O.MONO O.DFUN, 1, holeDFun, [], [n])
        val goalN = makeMem (I, H) (n, holeDom)
      in
        |>: goalDFun >: goalDom >: goalCod >: goalN #> (I, H, holeCod)
      end

    fun PathApp _ jdg =
      let
        val _ = RedPrlLog.trace "Synth.PathApp"
        val (I, H) >> CJ.SYNTH tm = jdg
        val Syn.PATH_APP (m, r) = Syn.out tm
        val (goalPathTy, holePathTy) = makeSynth (I, H) m
        val (goalLine, holeLine) = makeMatch (O.MONO O.PATH_TY, 0, holePathTy, [r], [])
      in
        |>: goalPathTy >: goalLine #> (I, H, holeLine)
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
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val Syn.VAR (x, _) = Syn.out m
        val Syn.VAR (y, _) = Syn.out n
        val _ = Assert.varEq (x, y)
        val catjdg = lookupHyp H x
        val ty' =
          case catjdg of
             CJ.TRUE ty => ty
           | _ => raise E.error [Fpp.text "Equality.Hyp: expected truth hypothesis"]

        (* If the types are identical, there is no need to create a new subgoal (which would amount to proving that 'ty' is a type).
           This is because the semantics of sequents is that by assuming that something is a member of a 'ty', we have
           automatically assumed that 'ty' is a type. *)
        val goalTy = makeEqTypeIfDifferent (I, H) (ty, ty')
      in
        |>:? goalTy #> (I, H, trivial)
      end
      handle Bind =>
        raise E.error [Fpp.text "Expected variable-equality sequent"]

    fun Custom sign _ jdg = 
      let
        val _ = RedPrlLog.trace "Equality.Custom"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg

        val Abt.$ (O.POLY (O.CUST (name, _, _)), args) = Abt.out m
        val true = Abt.eq (m, n)

        val {spec = ([],H') >> CJ.TRUE specTy, state = Lcf.|> (psi, _), ...} = Sig.lookup sign name
        val metas = Lcf.Tl.foldr (fn (x, jdg, r) => (x, RedPrlJudgment.sort jdg) :: r) [] psi
        val rho = ListPair.foldl (fn ((x, vl), arg, rho) => Metavar.Ctx.insert rho x (checkb (arg, vl))) Metavar.Ctx.empty (metas, args)
        val specTy' = substMetaenv rho specTy
        val _ = if Hyps.isEmpty H' then () else raise Fail "Equality.Custom only works with empty sequent"

        val goalTy = makeEqTypeIfDifferent (I, H) (ty, specTy')
      in
        |>:? goalTy #> (I, H, trivial)
      end

    fun Symmetry _ jdg =
      let
        val _ = RedPrlLog.trace "Equality.Symmetry"
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val goal = makeEq (I, H) ((n, m), ty)
      in
        |>: goal #> (I, H, trivial)
      end

    local
      fun jdgEqGoals (I, H) (jdg1, jdg2) = 
        case (jdg1, jdg2) of
           (CJ.TRUE ty1, CJ.TRUE ty2) => [makeEqType (I, H) (ty1, ty2)]
         | (CJ.EQ_TYPE (ty11, ty12), CJ.EQ_TYPE (ty21, ty22)) =>
             [makeEqType (I, H) (ty11, ty21),
              makeEqType (I, H) (ty12, ty22)]
         | (CJ.EQ ((m1, n1), ty1), CJ.EQ ((m2, n2), ty2)) =>
             [makeEqType (I, H) (ty1, ty2),
              makeEq (I, H) ((m1, m2), ty1),
              makeEq (I, H) ((n1, n2), ty1)]
         | _ => raise Fail "Judgments don't match"

      fun jdgWfGoals (I, H) jdg = 
        jdgEqGoals (I, H) (jdg, jdg)
    in
      fun EqElim z alpha jdg = 
        let
          val (I, H) >> CJ.TRUE mainGoal = jdg
          val CJ.EQ ((m, n), ty) = lookupHyp H z
          val x = alpha 0
          val Hx = H @> (x, CJ.TRUE ty)
          val (motiveGoal, motiveHole) = makeTerm (I, Hx) O.EXP

          val motiven = substVar (n, x) motiveHole
          val motivem = substVar (m, x) motiveHole

          val (rewrittenGoal, rewrittenHole) = makeTrue (I, H) motiven

          val motiveWfGoal = makeType (I, Hx) motiveHole
          val motiveMatchesMainGoal = makeEqType (I, H) (motivem, mainGoal)
        in
          |>: motiveGoal >: rewrittenGoal >: motiveWfGoal >: motiveMatchesMainGoal #> (I, H, rewrittenHole)
        end
      end
  end

  structure Coe =
  struct
    fun Eq alpha jdg =
      let
        val _ = RedPrlLog.trace "Coe.Eq"
        val (I, H) >> CJ.EQ ((lhs, rhs), ty) = jdg
        val Syn.COE {dir=(r0, r'0), ty=(u0, ty0), coercee=m0} = Syn.out lhs
        val Syn.COE {dir=(r1, r'1), ty=(u1, ty1), coercee=m1} = Syn.out rhs
        val () = Assert.paramEq "Coe.Eq source of direction" (r0, r1)
        val () = Assert.paramEq "Coe.Eq target of direction" (r'0, r'1)

        (* type *)
        val w = alpha 0
        val ty0w = substSymbol (P.ret w, u0) ty0
        val ty1w = substSymbol (P.ret w, u1) ty1
        val goalTy = makeEqType (I @ [(w, P.DIM)], H) (ty0w, ty1w)
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r' = substSymbol (r'0, u0) ty0
        val goalTy0 = makeEqTypeIfDifferent (I, H) (ty0r', ty)

        (* coercee *)
        val ty0r = substSymbol (r0, u0) ty0
        val goalCoercees = makeEq (I, H) ((m0, m1), ty0r)
      in
        |>: goalCoercees >:? goalTy0 >: goalTy #> (I, H, trivial)
      end

    fun CapEqL _ jdg =
      let
        val _ = RedPrlLog.trace "Coe.CapEq"
        val (I, H) >> CJ.EQ ((coe, other), ty) = jdg
        val Syn.COE {dir=(r, r'), ty=(u0, ty0), coercee=m} = Syn.out coe
        val () = Assert.paramEq "Coe.CapEq source and target of direction" (r, r')

        (* type *)
        val goalTy = makeType (I @ [(u0, P.DIM)], H) ty0
        (* after proving the above goal, [ty0r] must be a type *)
        val ty0r = substSymbol (r, u0) ty0
        val goalTy0 = makeEqTypeIfDifferent (I, H) (ty0r, ty)

        (* eq *)
        val goalEq = makeEq (I, H) ((m, other), ty)
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
        val (I, H) >> CJ.EQ ((m, n), ty) = jdg
        val m' = Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign) m
        val goal = makeEq (I, H) ((m', n), ty)
      in
        |>: goal #> (I, H, trivial)
      end
      handle _ => raise E.error [Fpp.text "EqHeadExpansion!"]

    fun EqTypeHeadExpansion sign _ jdg =
      let
        val _ = RedPrlLog.trace "Computation.EqTypeHeadExpansion"
        val (I, H) >> CJ.EQ_TYPE (ty1, ty2) = jdg
        val ty1' = Machine.eval sign Machine.CUBICAL (Machine.Unfolding.default sign) ty1
        val goal = makeEqType (I, H) (ty1', ty2)
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

  fun makeNamePopper alpha = 
    let
      val ix = ref 0
    in
      fn () => 
        let
          val i = !ix
          val h = alpha i
        in
          ix := i + 1;
          h
        end
    end

  fun CutLemma sign opid params alpha jdg = 
    let
      val fresh = makeNamePopper alpha

      val (I, H) >> catjdg = jdg

      val {spec, state = Lcf.|> (lemmaSubgoals, _), ...} = Sig.lookup sign opid
      val (I_spec, H_spec) >> specjdg = spec
      val _ = 
        if Hyps.isEmpty H_spec then () else 
          raise E.error [Fpp.text "Lemmas must have a categorical judgment as a conclusion"]

      val (rs, sigmas) = ListPair.unzip params

      val z = fresh ()
      val symenv = ListPair.foldlEq (fn ((x, _), r, rho) => Sym.Ctx.insert rho x r) Sym.Ctx.empty (I_spec, rs)

      fun processSubgoal ((I', H') >> cjdg) =
        let
          val I'' = List.map (fn (_, sigma) => (fresh (), sigma)) I'
          val symenv' = ListPair.foldlEq (fn ((u, _), (v, _), rho) => Sym.Ctx.insert rho u (P.ret v)) symenv (I', I'')
          val relabelingList = List.rev @@ Hyps.foldl (fn (x, cj, names) => (x, (fresh (), CJ.synthesis cj)) :: names) [] H'
          val relabelingDict = List.foldl (fn ((x,(y, _)), rho) => Sym.Ctx.insert rho x y) Sym.Ctx.empty relabelingList
          val H'' = Hyps.map (CJ.map_ (substSymenv symenv')) @@ Hyps.append H H'
        in
          (I'', List.map #2 relabelingList, RedPrlSequent.relabel relabelingDict @@ (I', H'') >> CJ.map_ (substSymenv symenv') cjdg)
        end

      val lemmaSubgoals' = Lcf.Tl.map processSubgoal lemmaSubgoals
      val specjdg' = CJ.map_ (substSymenv symenv) specjdg

      val lemmaExtract' =
        let
          val subgoalsList = Lcf.Tl.foldr (fn (x, (syms, vars, jdg), goals) => (x, (syms, vars, jdg)) :: goals) [] lemmaSubgoals'
          val valences = List.map (RedPrlJudgment.sort o #3 o #2) subgoalsList
          val arity = (valences, CJ.synthesis specjdg)
          fun argForSubgoal (x, (syms : (Sym.t * psort) list, vars : (Var.t * sort) list, _ >> cj)) = 
            let
              val us = List.map #1 syms
              val xs = List.map #1 vars
              val ps = List.map (fn (u, sigma) => (P.ret u, sigma)) syms
              val ms = List.map (fn (x, tau) => check (`x, tau)) vars
              val tau = CJ.synthesis cj
            in
              (us, xs) \ check (x $# (ps, ms), tau)
            end
        in
          O.POLY (O.CUST (opid, params, SOME arity)) $$ List.map argForSubgoal subgoalsList
        end

      val H' = H @> (z, specjdg')
      val (mainGoal, mainHole) = makeGoal @@ (I, H') >> catjdg

      val extract = substVar (lemmaExtract', z) mainHole
    in
      Lcf.Tl.map #3 lemmaSubgoals' >: mainGoal #> (I, H, extract)
    end

  fun Exact tm =
    Truth.Witness tm
      orelse_ Term.Exact tm



  val lookupRule = 
    fn "bool/eq/type" => Bool.EqType
     | "bool/eq/tt" => Bool.EqTT
     | "bool/eq/ff" => Bool.EqFF
     | "bool/eq/if" => Bool.ElimEq
     | "wbool/eq/type" => WBool.EqType
     | "wbool/eq/tt" => WBool.EqTT
     | "wbool/eq/ff" => WBool.EqFF
     | "wbool/eq/fcom" => WBool.EqFCom
     | "wbool/eq/wif" => WBool.ElimEq
     | "nat/eq/type" => Nat.EqType
     | "nat/eq/zero" => Nat.EqZero
     | "nat/eq/succ" => Nat.EqSucc
     | "nat/eq/nat-rec" => Nat.ElimEq
     | "int/eq/type" => Int.EqType
     | "int/eq/zero" => Int.EqZero
     | "int/eq/succ" => Int.EqSucc
     | "int/eq/negsucc" => Int.EqNegSucc
     | "void/eq/type" => Void.EqType
     | "S1/eq/type" => S1.EqType
     | "S1/eq/base" => S1.EqBase
     | "S1/eq/loop" => S1.EqLoop
     | "S1/eq/fcom" => S1.EqFCom
     | "S1/eq/S1-rec" => S1.ElimEq
     | "dfun/eq/type" => DFun.EqType
     | "dfun/eq/lam" => DFun.Eq
     | "dfun/intro" => DFun.True
     | "dfun/eq/eta" => DFun.Eta
     | "dfun/eq/app" => DFun.AppEq
     | "record/eq/type" => Record.EqType
     | "record/eq" => Record.Eq
     | "record/eq/eta" => Record.Eta
     | "record/eq/proj" => Record.ProjEq
     | "record/intro" => Record.True
     | "path/eq/type" => Path.EqType
     | "path/intro" => Path.True
     | "path/eq/abs" => Path.Eq
     | "path/eq/app" => Path.AppEq
     | "path/eq/app/const" => Path.AppConstCompute
     | "path/eq/eta" => Path.Eta
     | "hcom/eq" => HCom.Eq
     | "hcom/eq/cap" => HCom.CapEqL
     | "hcom/eq/tube" => HCom.TubeEqL

     | r => raise E.error [Fpp.text "No rule registered with name", Fpp.text r]


  local
    val CatJdgSymmetry : tactic =
      Equality.Symmetry orelse_ TypeEquality.Symmetry

    fun matchGoal f alpha jdg =
      f jdg alpha jdg
  in
    local
      fun StepTrue _ ty =
        case Syn.out ty of
           Syn.PATH_TY _ => Path.True
         | Syn.DFUN _ => DFun.True
         | Syn.RECORD _ => Record.True
         | _ => raise E.error [Fpp.text "Could not find introduction rule for", TermPrinter.ppTerm ty]

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
         | _ => raise E.error [Fpp.text "Could not find value equality rule for", TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n, Fpp.text "at type", TermPrinter.ppTerm ty]

      (* equality for neutrals: variables and elimination forms;
       * this includes structural equality and typed computation principles *)
      fun StepEqNeu sign (blocker1, blocker2) ((m, n), ty) =
        case (Syn.out m, blocker1, Syn.out n, blocker2) of
           (Syn.VAR _, _, Syn.VAR _, _) => Equality.Hyp
         | (Syn.WIF _, _, Syn.WIF _, _) => WBool.ElimEq
         | (Syn.IF _, _, Syn.IF _, _) => Bool.ElimEq
         | (Syn.IF _, Machine.VAR z, _, _) => Bool.EqElim z
         | (_, _, Syn.IF _, Machine.VAR z) => CatJdgSymmetry then_ Bool.EqElim z
         | (Syn.S1_REC _, _, Syn.S1_REC _, _) => S1.ElimEq
         | (Syn.APP _, _, Syn.APP _, _) => DFun.AppEq
         | (Syn.PROJ _, _, Syn.PROJ _, _) => Record.ProjEq
         | (Syn.PATH_APP (_, P.VAR _), _, Syn.PATH_APP (_, P.VAR _), _) => Path.AppEq
         | (Syn.CUST, _, Syn.CUST, _) => Equality.Custom sign
         | (_, Machine.OPERATOR theta, _, _) => Computation.Unfold sign theta
         | _ => raise E.error [Fpp.text "Could not find neutral equality rule for", TermPrinter.ppTerm m, Fpp.text "and", TermPrinter.ppTerm n, Fpp.text "at type", TermPrinter.ppTerm ty]

      fun StepEqNeuExpand sign blocker ty =
        case (blocker, Syn.out ty) of
           (_, Syn.DFUN _) => DFun.Eta
         | (_, Syn.PATH_TY _) => Path.Eta
         | (_, Syn.RECORD _) => Record.Eta
         | (Machine.OPERATOR theta, _) => Computation.Unfold sign theta
         | _ => raise E.error [Fpp.text "Could not expand neutral term of type", TermPrinter.ppTerm ty]


      structure HCom =
      struct
        open HCom

        val AutoEqL = CapEqL orelse_ TubeEqL orelse_ Eq

        (* Try all the hcom rules.
         * Note that the EQ rule is invertible only when the cap and tube rules fail. *)
        val AutoEqLR =
          CapEqL
            orelse_ (CatJdgSymmetry then_ HCom.CapEqL)
            orelse_ HCom.TubeEqL
            orelse_ (CatJdgSymmetry then_ HCom.TubeEqL)
            orelse_ HCom.Eq
      end

      structure Coe =
      struct
       open Coe

       val CapEqR = CatJdgSymmetry then_ CapEqL
       val AutoEqLR = CapEqL orelse_ CapEqR orelse_ Eq
       val AutoEqL = CapEqL orelse_ Eq
       val AutoEqR = CapEqR orelse_ Eq
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
         | (Syn.PATH_APP (_, P.APP _), _, _, _) => Path.AppConstCompute
         | (_, _, Syn.PATH_APP (_, P.APP _), _) => CatJdgSymmetry then_ Path.AppConstCompute
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
        (fn _ >> CJ.TRUE ty => StepTrue sign ty
          | _ >> CJ.EQ_TYPE tys => StepEqType sign tys
          | _ >> CJ.EQ ((m, n), ty) => StepEq sign ((m, n), ty)
          | _ >> CJ.SYNTH m => StepSynth sign m
          | _ >> CJ.PARAM_SUBST _ => Misc.ParamSubst
          | MATCH _ => Misc.MatchOperator
          | MATCH_RECORD _ => Record.MatchRecord orelse_ Computation.MatchRecordHeadExpansion sign then_ Record.MatchRecord)


      fun isWfJdg (CJ.TRUE _) = false
        | isWfJdg _ = true

      structure HypsUtil = TelescopeUtil (Hyps)

      fun FindHyp alpha ((I, H) >> jdg) =
        if isWfJdg jdg then
          case HypsUtil.search H (fn jdg' => CJ.eq (jdg, jdg')) of
             SOME (lbl, _) => Hyp.Project lbl alpha ((I, H) >> jdg)
           | NONE => raise E.error [Fpp.text "Could not find suitable hypothesis"]
        else
          raise E.error [Fpp.text "Non-deterministic tactics can only be run on auxiliary goals"]
    in
      fun AutoStep sign alpha jdg = 
        StepJdg sign alpha jdg
          handle exn => 
            FindHyp alpha jdg
            handle _ => raise exn
    end

    local
      fun StepTrue ty =
        case Syn.out ty of
           Syn.BOOL => Bool.Elim
         | Syn.WBOOL => WBool.Elim
         | Syn.NAT => Nat.Elim
         | Syn.VOID => Void.Elim
         | Syn.S1 => S1.Elim
         | Syn.DFUN _ => DFun.Elim
         | Syn.PATH_TY _ => Path.Elim
         | Syn.RECORD _ => Record.Elim
         | _ => raise E.error [Fpp.text "Could not find suitable elimination rule for", TermPrinter.ppTerm ty]

      fun StepEq ty =
        case Syn.out ty of
           Syn.BOOL => Bool.EqElim
         | _ => raise E.error [Fpp.text "Could not find suitable elimination rule for", TermPrinter.ppTerm ty]

      fun StepJdg _ z alpha jdg =
        let
          val (_, H) >> catjdg = jdg
        in
          case lookupHyp H z of
             CJ.TRUE hyp =>
              (case catjdg of
                  CJ.TRUE _ => StepTrue hyp z alpha jdg
                | CJ.EQ _ => StepEq hyp z alpha jdg
                | _ => raise E.error [Fpp.text ("Could not find suitable elimination rule [TODO, display information]")])
           | CJ.EQ _ => Equality.EqElim z alpha jdg
           | _ => raise E.error [Fpp.text "Could not find suitable elimination rule"]
        end
    in
      val Elim = StepJdg
    end

  end
end
