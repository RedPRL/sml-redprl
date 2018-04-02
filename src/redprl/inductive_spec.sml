structure InductiveSpec : INDUCTIVE_SPEC =
struct
  structure Abt = RedPrlAbt and Ast = RedPrlAst and Syn = SyntaxView
  structure AJ = AtomicJudgment
  structure E = RedPrlError and K = RedPrlKind and O = RedPrlOpData
  val >> = Sequent.>>
  infix >>
  fun @@ (f, x) = f x
  infixr @@
  fun @> (H, (x, j)) = Sequent.Hyps.snoc H x j
  infix @>

  type conid = string
  type decl = RedPrlAbt.abt (* XXX *)
  type constr = RedPrlAbt.abt (* XXX *)
  type constrs = (conid * constr) list
  type decl_args = RedPrlAbt.abt RedPrlAbt.bview list
  type args = RedPrlAbt.abt list

  val IND_SPECTYPE_SELF = Syn.into Syn.IND_SPECTYPE_SELF

  structure ConstrDict = StringListDict
  structure SpecCtx = Var.Ctx
  structure DimSet = ListSet (structure Elem = Sym.Ord)
  type specctx = Abt.abt SpecCtx.dict
  type dimset = DimSet.set

  (* TODO tail recursion *)

  fun EqSpecType H ((ty0, ty1), level) =
    case (Syn.out ty0, Syn.out ty1) of
       (Syn.IND_SPECTYPE_SELF, Syn.IND_SPECTYPE_SELF) => []
     | (Syn.IND_SPECTYPE_FUN (a0, x, b0x), Syn.IND_SPECTYPE_FUN (a1, y, b1y)) =>
         let
           val z = Sym.new ()
           val b0z = VarKit.rename (z, x) b0x
           val b1z = VarKit.rename (z, y) b1y
           (* favonia: more research needed for other kinds *)
           val seqA = H >> AJ.EQ ((a0, a1), Syn.intoU (level, K.COE))
         in
           seqA :: EqSpecType (H @> (z, AJ.TRUE a0)) ((b0z, b1z), level)
         end

  fun SpecType H (ty, level) = EqSpecType H ((ty, ty), level)

  (* The following checker type-checks more expressions than the rules
   * on paper because `($ (lam [_] foo) junk)` and `(fcom 0~>0 m [... junk])` are allowed.
   * This is to solve the difficulty to generate a valid type for `junk`
   * in the first case. One easy solution is to beta-reduce everything first.
   *
   * This extension is implemented as `untypedReduce`.
   *
   * -favonia
   *)

  fun untypedReduce tm : Abt.abt =
    case Syn.out tm of
       Syn.VAR _ => tm
     | Syn.IND_SPEC_INTRO params => tm
     | Syn.IND_SPEC_FCOM {dir, cap, ...} =>
         if Abt.eq dir then cap else tm
     | Syn.IND_SPEC_LAM (x, ax) =>
         Syn.into (Syn.IND_SPEC_LAM (x, untypedReduce ax))
     | Syn.IND_SPEC_APP (a, b) =>
         case Syn.out (untypedReduce a) of
            Syn.IND_SPEC_LAM (x, ax) => untypedReduce (Abt.substVar (b, x) ax)
          | a => Syn.into (Syn.IND_SPEC_APP (Syn.into a, b))

  (* the invariant is that tm0 and tm1 should be eta-long and lam/app-reduced *)
  (* TODO optimization: [intro] and [fcom] will not show up after [app] *)
  fun SynthReduced H (constrs, specctx) (tm0, tm1) =
    case (Syn.out tm0, Syn.out tm1) of
       (Syn.VAR (x, _), Syn.VAR (y, _)) =>
         let
           val true = Sym.eq (x, y)
           val ty = SpecCtx.lookup specctx x
         in
           (ty, [])
         end
     | (Syn.IND_SPEC_APP (m0, n0), Syn.IND_SPEC_APP (m1, n1)) =>
         let
           val (ty, seqsM) = SynthReduced H (constrs, specctx) (m0, m1)
           val Syn.IND_SPECTYPE_FUN (a0, x, b0x) = Syn.out ty
           val seqN = H >> AJ.EQ ((n0, n1), a0)
         in
           (Abt.substVar (n0, x) b0x, seqsM @ [seqN])
         end
     | (tm0', tm1') =>
         (case (simplifyConstr H (constrs, specctx) tm0', simplifyConstr H (constrs, specctx) tm1') of
            (SOME (tm0, goals0), SOME (tm1, goals1)) =>
              (IND_SPECTYPE_SELF, goals0 @ goals1 @ EqSpec H (constrs, specctx) ((tm0, tm1), IND_SPECTYPE_SELF))
          | (SOME (tm0, goals0), NONE) =>
              (IND_SPECTYPE_SELF, goals0 @ EqSpec H (constrs, specctx) ((tm0, tm1), IND_SPECTYPE_SELF))
          | (NONE, SOME (tm1, goals1)) =>
              (IND_SPECTYPE_SELF, goals1 @ EqSpec H (constrs, specctx) ((tm0, tm1), IND_SPECTYPE_SELF))
          | (NONE, NONE) =>
              (case (tm0', tm1') of
                 (Syn.IND_SPEC_FCOM params0, Syn.IND_SPEC_FCOM params1) =>
                   (IND_SPECTYPE_SELF, EqSpecFCom H (constrs, specctx) (params0, params1))
               | (Syn.IND_SPEC_INTRO params0, Syn.IND_SPEC_INTRO params1) =>
                   (IND_SPECTYPE_SELF, EqSpecIntro H (constrs, specctx) (params0, params1))))

  and EqSpec H (constrs, specctx) (((tm0, tm1), ty) : (Abt.abt * Abt.abt) * Abt.abt)=
    case Syn.out ty of
       Syn.IND_SPECTYPE_FUN (a, z, bz) =>
         let
           val w = Sym.new ()
           val bw = VarKit.rename (w, z) bz
         in
           EqSpec (H @> (w, AJ.TRUE a)) (constrs, specctx)
             ((Syn.into (Syn.IND_SPEC_APP (tm0, VarKit.toExp w)),
               Syn.into (Syn.IND_SPEC_APP (tm1, VarKit.toExp w))), bw)
         end
     | Syn.IND_SPECTYPE_SELF =>
         let
           val (ty, goals) = SynthReduced H (constrs, specctx)
             (untypedReduce tm0, untypedReduce tm1)
         in
           case Syn.out ty of Syn.IND_SPECTYPE_SELF => goals
         end

  and EqSpecIfDifferent H (constrs, specctx) ((tm0, tm1), ty) =
    if Abt.eq (tm0, tm1) then [] else EqSpec H (constrs, specctx) ((tm0, tm1), ty)

  and restrictedEqSpec eqs H (constrs, specctx) ((tm0, tm1), ty) =
    case Restriction.restrict eqs of
       SOME f => EqSpec
         (Sequent.Hyps.map (AJ.map f) H)
         (ConstrDict.map f constrs, SpecCtx.map f specctx)
         ((f tm0, f tm1), f ty)
     | NONE => []

  and restrictedEqSpecIfDifferent eqs H (constrs, specctx) ((tm0, tm1), ty) =
    case Restriction.restrict eqs of
       SOME f => EqSpecIfDifferent
         (Sequent.Hyps.map (AJ.map f) H)
         (ConstrDict.map f constrs, SpecCtx.map f specctx)
         ((f tm0, f tm1), f ty)
     | NONE => []

  and EqSpecInterTube H (constrs, specctx) w (tubes0, tubes1) =
    let
      val tubes0 = VarKit.alphaRenameTubes w tubes0
      val tubes1 = VarKit.alphaRenameTubes w tubes1

      val goalsOnDiag = List.concat @@
        ListPair.mapEq
          (fn ((eq, t0), (_, t1)) =>
            restrictedEqSpec [eq]
              (H @> (w, AJ.TERM O.DIM))
              (constrs, specctx)
              ((t0, t1), IND_SPECTYPE_SELF))
          (tubes0, tubes1)

      val goalsNotOnDiag = List.concat @@
        ListPairUtil.enumInterExceptDiag
          (fn ((eq0, t0), (eq1, t1)) =>
            restrictedEqSpecIfDifferent [eq0, eq1]
              (H @> (w, AJ.TERM O.DIM))
              (constrs, specctx)
              ((t0, t1), IND_SPECTYPE_SELF))
          (tubes0, tubes1)
    in
      goalsOnDiag @ goalsNotOnDiag
    end

  and EqSpecCapTubeIfDifferent H (constrs, specctx) (cap, (r, tubes)) = List.concat @@
    List.map
      (fn (eq, (u, tube)) =>
        restrictedEqSpecIfDifferent [eq] H (constrs, specctx)
          ((cap, Abt.substVar (r, u) tube), IND_SPECTYPE_SELF))
      tubes

  and EqSpecFCom H (constrs, specctx)
    ({dir=dir0, cap=cap0, tubes=tubes0},
     {dir=dir1, cap=cap1, tubes=tubes1}) =
    let
      val _ = Assert.dirEq "EqSpecFCom direction" (dir0, dir1)

      val eqs0 = List.map #1 tubes0
      val eqs1 = List.map #1 tubes1
      val _ = Assert.equationsEq "EqSpecFCom equations" (eqs0, eqs1)
      val _ = Assert.tautologicalEquations "EqSpecFCom tautology checking" eqs0

      val goalsCap = EqSpec H (constrs, specctx) ((cap0, cap1), IND_SPECTYPE_SELF)
      val w = Sym.new ()
      val goalsInterTube = EqSpecInterTube H (constrs, specctx) w (tubes0, tubes1)
      val goalsCapTube = EqSpecCapTubeIfDifferent H (constrs, specctx) (cap0, (#1 dir0, tubes0))
    in
      goalsCap @ goalsInterTube @ goalsCapTube
    end

  and simplifyFcomTube H (constrs, specctx) {dir, cap, tubes} =
    Option.map
      (fn (_, (u, tube)) =>
        let
          val w = Sym.new ()
          val goalsInterTube = EqSpecInterTube H (constrs, specctx) w (tubes, tubes)
          val goalsCapTube = EqSpecCapTubeIfDifferent H (constrs, specctx) (cap, (#1 dir, tubes))
        in
          (Abt.substVar (#2 dir, u) tube, goalsInterTube @ goalsCapTube)
        end)
    (List.find (fn (eq, _) => Abt.eq eq) tubes)

  and EqSpecIntro H (constrs, specctx) ((label0, args0), (label1, args1)) =
    let
      val true = label0 = label1
      fun seqs' (([], []), Syn.IND_CONSTR_DISCRETE _) = []
        | seqs' (([], []), Syn.IND_CONSTR_KAN _) = []
        | seqs' ((arg0::args0, arg1::args1), Syn.IND_CONSTR_FUN (a,x,bx)) =
            let
              val seq = H >> AJ.EQ ((arg0, arg1), a)
            in
              seq :: seqs ((args0, args1), Abt.substVar (arg0, x) bx)
            end
        | seqs' ((arg0::args0, arg1::args1), Syn.IND_CONSTR_SPEC_FUN (a,x,bx)) =
            let
              val seqsSpec = EqSpec H (constrs, specctx) ((arg0, arg1), a)
            in
              seqsSpec @ seqs ((args0, args1), Abt.substVar (arg0, x) bx)
            end
        | seqs' ((arg0::args0, arg1::args1), Syn.IND_CONSTR_LINE (x,bx)) =
            let
              (* XXX no sort-checking *)
              val _ = Assert.alphaEq (arg0, arg1)
            in
              seqs ((args0, args1), Abt.substVar (arg0, x) bx)
            end
      and seqs (argsPair, spec) = seqs' (argsPair, Syn.out spec)
    in
      seqs ((args0, args1), ConstrDict.lookup constrs label0)
    end

  and simplifyIntro H (constrs, specctx) (label, args) =
    let
      fun trySimplify' ([], Syn.IND_CONSTR_DISCRETE boundaries) =
            Option.map (fn (_, boundary) => (boundary, []))
              (List.find (fn (eq, _) => Abt.eq eq) boundaries)
        | trySimplify' ([], Syn.IND_CONSTR_KAN boundaries) =
            Option.map (fn (_, boundary) => (boundary, []))
              (List.find (fn (eq, _) => Abt.eq eq) boundaries)
        | trySimplify' (arg::args, Syn.IND_CONSTR_FUN (a,x,bx)) =
            Option.map
              (fn (boundary, seqs) =>
                let
                  val seq = H >> AJ.MEM (arg, a)
                in
                  (boundary, seq :: seqs)
                end)
              (trySimplify (args, Abt.substVar (arg, x) bx))
        | trySimplify' (arg::args, Syn.IND_CONSTR_SPEC_FUN (a,x,bx)) =
            Option.map
              (fn (boundary, seqs) =>
                let
                  val seqsSpec = EqSpec H (constrs, specctx) ((arg, arg), a)
                in
                  (boundary, seqsSpec @ seqs)
                end)
              (trySimplify (args, Abt.substVar (arg, x) bx))
        | trySimplify' (arg::args, Syn.IND_CONSTR_LINE (x,bx)) =
            (* XXX no sort-checking *)
            trySimplify (args, Abt.substVar (arg, x) bx)
      and trySimplify (args, spec) = trySimplify' (args, Syn.out spec)
    in
      trySimplify (args, ConstrDict.lookup constrs label)
    end

  and simplifyConstr H (constrs, specctx) =
    fn Syn.IND_SPEC_INTRO args => simplifyIntro H (constrs, specctx) args
     | Syn.IND_SPEC_FCOM args => simplifyFcomTube H (constrs, specctx) args

  fun EqSpecInterBoundary H (constrs, specctx) boundaries =
    let
      val seqsOnDiag = List.concat @@
        List.map
          (fn (eq, b) =>
            restrictedEqSpec [eq] H (constrs, specctx)
              ((b, b), IND_SPECTYPE_SELF))
          boundaries

      val seqsNotOnDiag = List.concat @@
        ListPairUtil.enumInterExceptDiag
          (fn ((eq0, b0), (eq1, b1)) =>
            restrictedEqSpecIfDifferent [eq0, eq1] H (constrs, specctx)
              ((b0, b1), IND_SPECTYPE_SELF))
          (boundaries, boundaries)
    in
      seqsOnDiag @ seqsNotOnDiag
    end

  (* Is it okay to move dimensions upfront? It is banned in Part IV,
   * and the parser disallows it, but the checker here allows this.
   *
   * (Oops, the parser has not banned it yet.)
   *)
  fun checkConstr' (H, dimset) (constrs, specctx) constr level =
    case Syn.out constr of
       Syn.IND_CONSTR_DISCRETE [] => [] (* XXX more refined criterion *)
     | Syn.IND_CONSTR_KAN boundaries =>
         let
           val eqs = List.map #1 boundaries
           fun inSet dim =
             case Syn.out dim of
                Syn.DIM0 => true
              | Syn.DIM1 => true
              | Syn.VAR (v, _) => DimSet.member dimset v
           val true = List.all (fn (r0, r1) => inSet r0 andalso inSet r1) eqs
           val _ = Assert.tautologicalEquations "checkConstr' tautology checking" eqs
         in
           EqSpecInterBoundary H (constrs, specctx) boundaries
         end
     | Syn.IND_CONSTR_FUN (a,x,bx) =>
         let
           val w = Sym.new () (* is it possible to save this? *)
           val seq = H >> AJ.MEM (a, Syn.intoU (level, K.COE))
           val rest = checkConstr' (H @> (w, AJ.TRUE a), dimset) (constrs, specctx) (VarKit.rename (w, x) bx) level
         in
           seq :: rest
         end
     | Syn.IND_CONSTR_SPEC_FUN (a,x,bx) =>
         let
           val w = Sym.new () (* is it possible to save this? *)
           val seqs = SpecType H (a, level)
           val rest = checkConstr' (H, dimset) (constrs, SpecCtx.insert specctx w a) (VarKit.rename (w, x) bx) level
         in
           seqs @ rest
         end
     | Syn.IND_CONSTR_LINE (x,bx) =>
         let
           val w = Sym.new () (* is it possible to save this? *)
         in
           checkConstr' (H @> (w, AJ.TERM O.DIM), DimSet.insert dimset w) (constrs, specctx) (VarKit.rename (w, x) bx) level
         end
  fun checkConstr H constrs constr level =
    checkConstr' (H, DimSet.empty) (constrs, SpecCtx.empty) constr level

  fun checkConstrs H constrs level = List.concat @@ List.rev @@ #2 @@
    List.foldl
      (fn ((label, constr), (prefix, accumulatedGoals)) =>
        let
          val newseqs = checkConstr H prefix constr level
          val (prefix, present) = ConstrDict.insert' prefix label constr
          val _ = if present then E.raiseError (E.GENERIC [Fpp.text "Duplicate constructors"]) else ()
        in
          (prefix, newseqs :: accumulatedGoals)
        end)
      (ConstrDict.empty, [])
      constrs

  fun checkDecl' H decl =
    case Syn.out decl of
       Syn.IND_FAM_BASE (level, constrs) => checkConstrs H constrs level
     | Syn.IND_FAM_FUN (a,x,bx) =>
         let
           val w = Sym.new () (* can we avoid this? *)
           val seq = H >> AJ.TYPE (a, K.top)
         in
           seq :: checkDecl' (H @> (w, AJ.TRUE a)) (VarKit.rename (w, x) bx)
         end
     | Syn.IND_FAM_LINE (x,bx) =>
         let
           val w = Sym.new () (* can we avoid this? *)
         in
           checkDecl' (H @> (w, AJ.TERM O.DIM)) (VarKit.rename (w, x) bx)
         end
  val checkDecl = checkDecl' Sequent.Hyps.empty

  open ArityNotation infix ->> |:

  type precomputed_valences =
    {tyVls: RedPrlArity.valence list,
     introExtraVls: RedPrlArity.valence list ConstrDict.dict,
     elimCasesVls: RedPrlArity.valence list}

  fun eqPrecomputedValences
    ({tyVls=tyVls0, introExtraVls=introExtraVls0, elimCasesVls=elimCasesVls0},
     {tyVls=tyVls1, introExtraVls=introExtraVls1, elimCasesVls=elimCasesVls1})
    = tyVls0 = tyVls1 andalso
      ConstrDict.toList introExtraVls0 = ConstrDict.toList introExtraVls1 andalso
      elimCasesVls0 = elimCasesVls1


  local
    fun computeIntroAndElimCase constr =
      case Ast.out constr of
         Ast.$ (O.IND_CONSTR_DISCRETE, _) => ([], [])
       | Ast.$ (O.IND_CONSTR_KAN, _) => ([], [])
       | Ast.$ (O.IND_CONSTR_FUN, [_, Ast.\ (_, bx)]) =>
           let
             val (introVls, caseBindings) = computeIntroAndElimCase bx
           in
             (([] |: O.EXP) :: introVls, O.EXP :: caseBindings)
           end
       | Ast.$ (O.IND_CONSTR_SPEC_FUN, [_, Ast.\ (_, bx)]) =>
           let
             val (introVls, caseBindings) = computeIntroAndElimCase bx
           in
             (([] |: O.EXP) :: introVls, O.EXP :: O.EXP :: caseBindings)
           end
       | Ast.$ (O.IND_CONSTR_LINE, [Ast.\ (_, bx)]) =>
           let
             val (introVls, caseBindings) = computeIntroAndElimCase bx
           in
             (([] |: O.DIM) :: introVls, O.DIM :: caseBindings)
           end
  in
    fun computeValences decl =
      case Ast.out decl of
         Ast.$ (O.IND_FAM_BASE conids, lvl :: constrs) =>
           let
             val (introVls, elimCasesVls) =
               ListPair.foldlEq
                 (fn (conid, Ast.\ (_, constr), (dict, elimCasesVls)) =>
                   let
                     val (introVls, binding) = computeIntroAndElimCase constr
                     val (dict, false) = ConstrDict.insert' dict conid introVls
                   in
                     (dict, (binding |: O.EXP) :: elimCasesVls)
                   end)
                 (ConstrDict.empty, [])
                 (conids, constrs)
           in
             {tyVls=[],
              introExtraVls=introVls,
              elimCasesVls=elimCasesVls}
           end
       | Ast.$ (O.IND_FAM_FUN, [_, Ast.\ (_, bx)]) =>
           let
             val {tyVls, introExtraVls, elimCasesVls} = computeValences bx
           in
             {tyVls=([] |: O.EXP) :: tyVls,
              introExtraVls=introExtraVls,
              elimCasesVls=elimCasesVls}
           end
       | Ast.$ (O.IND_FAM_LINE, [Ast.\ (_, bx)]) =>
           let
             val {tyVls, introExtraVls, elimCasesVls} = computeValences bx
           in
             {tyVls=([] |: O.DIM) :: tyVls,
              introExtraVls=introExtraVls,
              elimCasesVls=elimCasesVls}
           end

    fun getTypeValences {tyVls, introExtraVls, elimCasesVls} = tyVls

    fun getIntroValences {tyVls, introExtraVls, elimCasesVls} conid =
      tyVls @ ConstrDict.lookup introExtraVls conid

    fun getElimCasesValences {tyVls, introExtraVls, elimCasesVls} = elimCasesVls
  end

  local
    fun computeSpecIntroValences constr =
      case Ast.out constr of
         Ast.$ (O.IND_CONSTR_DISCRETE, _) => []
       | Ast.$ (O.IND_CONSTR_KAN, _) => []
       | Ast.$ (O.IND_CONSTR_FUN, [_, Ast.\ (_, bx)]) => ([] |: O.EXP) :: computeSpecIntroValences bx
       | Ast.$ (O.IND_CONSTR_SPEC_FUN, [_, Ast.\ (_, bx)]) => ([] |: O.IND_SPEC) :: computeSpecIntroValences bx
       | Ast.$ (O.IND_CONSTR_LINE, [Ast.\ (_, bx)]) => ([] |: O.DIM) :: computeSpecIntroValences bx
  in
    fun computeAllSpecIntroValences decl =
      case Ast.out decl of
         Ast.$ (O.IND_FAM_BASE conids, lvl :: constrs) =>
           ListPair.foldlEq
             (fn (conid, Ast.\ (_, constr), dict) =>
               let
                 val (dict, false) = ConstrDict.insert' dict conid (computeSpecIntroValences constr)
               in
                 dict
               end)
             ConstrDict.empty
             (conids, constrs)
       | Ast.$ (O.IND_FAM_FUN, [_, Ast.\ (_, bx)]) => computeAllSpecIntroValences bx
       | Ast.$ (O.IND_FAM_LINE, [Ast.\ (_, bx)]) => computeAllSpecIntroValences bx
  end

  fun \\ t = Abt.\ ([], t)

  local
    fun fillFamily' varenv revTyArgs decl args =
      case (Syn.out decl, args) of
         (Syn.IND_FAM_BASE (_, l), _) => (List.rev revTyArgs, List.map (fn (conid, constr) => (conid, Abt.substVarenv varenv constr)) l, args)
       | (Syn.IND_FAM_FUN (_,x,bx), arg::args) =>
            fillFamily' (Var.Ctx.insert varenv x arg) (arg::revTyArgs) bx args
       | (Syn.IND_FAM_LINE (x,bx), arg::args) =>
            fillFamily' (Var.Ctx.insert varenv x arg) (arg::revTyArgs) bx args
  in
    fun fillFamily decl args = fillFamily' Var.Ctx.empty [] decl args
  end

  (* XXX Maybe `opid` should be `tyid`? *)

  fun substSpan varenv (r0, r1) = (Abt.substVarenv varenv r0, Abt.substVarenv varenv r1)

  fun intoType (opid, (declVls, precomputedVls), (declArgs, tyArgs)) =
    Abt.$$ (O.IND_TYPE (opid, SOME (declVls @ getTypeValences precomputedVls)),
            declArgs @ List.map \\ tyArgs)

  fun intoIntro (opid, (declVls, precomputedVls), (declArgs, tyArgs)) conid introArgs =
    Abt.$$
      (O.IND_INTRO (opid, conid, SOME (declVls @ getIntroValences precomputedVls conid)),
       declArgs @ List.map \\ tyArgs @ List.map \\ introArgs)

  fun realizeSpecType meta varenv ty =
    case Syn.out ty of
       Syn.IND_SPECTYPE_SELF => intoType meta
     | Syn.IND_SPECTYPE_FUN (a, x, bx) => Syn.into (Syn.FUN (Abt.substVarenv varenv a, x, realizeSpecType meta varenv bx))

  fun realizeSpecTerm (meta as (opid, (declVls, precomputedVls), (declArgs, tyArgs))) varenv term =
    case Syn.out term of
       Syn.VAR _ => Abt.substVarenv varenv term
     | Syn.IND_SPEC_INTRO params => realizeSpecIntro meta varenv params
     | Syn.IND_SPEC_FCOM params => realizeSpecFcom meta varenv params
     | Syn.IND_SPEC_LAM (x, mx) => Syn.intoLam (x, realizeSpecTerm meta varenv mx)
     | Syn.IND_SPEC_APP (m, n) => Syn.intoApp (realizeSpecTerm meta varenv m, Abt.substVarenv varenv n)
     | _ => term (* this is for normal terms. we can avoid this case by checking the valences *)

  and realizeSpecIntro meta varenv (conid, args) =
    (* a better version should check the variances and only realize the spec terms. *)
    intoIntro meta conid (List.map (realizeSpecTerm meta varenv) args)

  and realizeSpecFcom meta varenv {dir, cap, tubes} =
    Syn.intoFcom
      {dir = substSpan varenv dir,
       cap = realizeSpecTerm meta varenv cap,
       tubes = List.map (realizeTube meta varenv) tubes}

  and realizeTube meta varenv (eq, (u, term)) =
    (substSpan varenv eq, (u, realizeSpecTerm meta varenv term))

  fun realizeSpecBoundary meta varenv (eq, term) =
    (substSpan varenv eq, realizeSpecTerm meta varenv term)

  fun realizeSpecBoundaries meta varenv =
    List.map (realizeSpecBoundary meta varenv)

  local
    fun realizeIntroBoundaries' meta varenv constr args =
      case (Syn.out constr, args) of
         (Syn.IND_CONSTR_DISCRETE boundaries, []) =>
           realizeSpecBoundaries meta varenv boundaries
       | (Syn.IND_CONSTR_KAN boundaries, []) =>
           realizeSpecBoundaries meta varenv boundaries
       | (Syn.IND_CONSTR_FUN (_,x,bx), arg::args) =>
           realizeIntroBoundaries' meta (Var.Ctx.insert varenv x arg) bx args
       | (Syn.IND_CONSTR_SPEC_FUN (_,x,bx), arg::args) =>
           realizeIntroBoundaries' meta (Var.Ctx.insert varenv x arg) bx args
       | (Syn.IND_CONSTR_LINE (x,bx), arg::args) =>
           realizeIntroBoundaries' meta (Var.Ctx.insert varenv x arg) bx args
  in
    fun realizeIntroBoundaries meta constr args =
      realizeIntroBoundaries' meta Var.Ctx.empty constr args
  end

  local
    fun recResult plug specTy arg =
      case Syn.out specTy of
         Syn.IND_SPECTYPE_SELF => plug arg
       | Syn.IND_SPECTYPE_FUN (_,x,bx) => Syn.intoLam (x, recResult plug bx (Syn.intoApp (arg, VarKit.toExp x)))

    fun createVarenvForBranch plug acc (constr, vars, introArgs) =
      case (Syn.out constr, vars, introArgs) of
         (Syn.IND_CONSTR_DISCRETE _, [], []) => acc
       | (Syn.IND_CONSTR_KAN _, [], []) => acc
       | (Syn.IND_CONSTR_FUN (_,_,bx), var::vars, arg::introArgs) =>
            createVarenvForBranch plug (Var.Ctx.insert acc var arg) (bx, vars, introArgs)
       | (Syn.IND_CONSTR_SPEC_FUN (a,_,bx), var::recvar::vars, arg::introArgs) =>
            let
              val acc = Var.Ctx.insert acc var arg
              val acc = Var.Ctx.insert acc recvar (recResult plug a arg)
            in
              createVarenvForBranch plug acc (bx, vars, introArgs)
            end
       | _ => E.raiseError (E.IMPOSSIBLE (Fpp.text "createVarenv"))
  in
    fun fillBranch plug constr (vars, branch) introArgs =
      Abt.substVarenv (createVarenvForBranch plug Var.Ctx.empty (constr, vars, introArgs)) branch
  end

  local
    fun stepCoeIntro' (dir as (r, r')) (z, (meta, varenv, conid, constr)) revCoercedArgs introArgs =
      case (Syn.out constr, introArgs) of
         (Syn.IND_CONSTR_DISCRETE [], []) => intoIntro meta conid (List.rev revCoercedArgs)
       | (Syn.IND_CONSTR_KAN boundaries, []) =>
            let
              fun makeTube (eq, term) =
                (substSpan varenv eq,
                 (z,
                  Syn.intoCoe
                    {dir = (VarKit.toDim z, r'),
                     ty = (z, intoType meta),
                     coercee = realizeSpecTerm meta varenv term}))
            in
              Syn.intoFcom
                {dir = (r', r),
                 cap = intoIntro meta conid (List.rev revCoercedArgs),
                 tubes = List.map makeTube boundaries}
            end
       | (Syn.IND_CONSTR_FUN (a, x, bx), arg::introArgs) =>
            let
              fun coe r' = Syn.intoCoe
                {dir = (#1 dir, r'),
                 ty = (z, Abt.substVarenv varenv a),
                 coercee = arg}
              val varenv' = Var.Ctx.insert varenv x (coe (VarKit.toDim z))
              val revCoercedArgs' = coe r' :: revCoercedArgs
            in
              stepCoeIntro' dir (z, (meta, varenv', conid, bx)) revCoercedArgs' introArgs
            end
       | (Syn.IND_CONSTR_SPEC_FUN (a, x, bx), arg::introArgs) =>
            let
              fun coe r' = Syn.intoCoe
                {dir = (#1 dir, r'),
                 ty = (z, realizeSpecType meta varenv a),
                 coercee = arg}
              val varenv' = Var.Ctx.insert varenv x (coe (VarKit.toDim z))
              val revCoercedArgs' = coe r' :: revCoercedArgs
            in
              stepCoeIntro' dir (z, (meta, varenv', conid, bx)) revCoercedArgs' introArgs
            end
       | (Syn.IND_CONSTR_LINE (x, bx), arg::introArgs) =>
            let
              val varenv' = Var.Ctx.insert varenv x arg
              val revCoercedArgs' = Abt.substVar (r', z) arg :: revCoercedArgs
            in
              stepCoeIntro' dir (z, (meta, varenv', conid, bx)) revCoercedArgs' introArgs
            end
  in
    fun stepCoeIntro dir (z, (meta, conid, constr)) introArgs =
      stepCoeIntro' dir (z, (meta, Var.Ctx.empty, conid, constr)) [] introArgs
  end

  local
    fun EqTyArgs' H varenv decl (args0, args1) (univ as (level, kind)) =
      case (Syn.out decl, args0, args1) of
         (Syn.IND_FAM_BASE (l, _), [], []) =>
            let
              val () = Assert.View.levelLeq (l, level)
              val () = Assert.kindLeq (K.KAN, kind)
            in
              []
            end
       | (Syn.IND_FAM_FUN (a, x, bx), arg0::args0, arg1::args1) =>
            (H >> AJ.EQ ((arg0, arg1), Abt.substVarenv varenv a))
            :: EqTyArgs' H (Var.Ctx.insert varenv x arg0) bx (args0, args1) univ
       | (Syn.IND_FAM_LINE (x, bx), arg0::args0, arg1::args1) =>
            let val true = Abt.eq (arg0, arg1)
            in EqTyArgs' H (Var.Ctx.insert varenv x arg0) bx (args0, args1) univ
            end
  in
    fun EqType H = EqTyArgs' H Var.Ctx.empty
  end

  local
    fun EqIntroArgs' H meta varenv constr (args0, args1) =
      case (Syn.out constr, args0, args1) of
         (Syn.IND_CONSTR_DISCRETE _, [], []) => []
       | (Syn.IND_CONSTR_KAN _, [], []) => []
       | (Syn.IND_CONSTR_FUN (a, x, bx), arg0::args0, arg1::args1) =>
            (H >> AJ.EQ ((arg0, arg1), Abt.substVarenv varenv a))
            :: EqIntroArgs' H meta (Var.Ctx.insert varenv x arg0) bx (args0, args1)
       | (Syn.IND_CONSTR_SPEC_FUN (a, x, bx), arg0::args0, arg1::args1) =>
            (H >> AJ.EQ ((arg0, arg1), realizeSpecType meta varenv a))
            :: EqIntroArgs' H meta (Var.Ctx.insert varenv x arg0) bx (args0, args1)
       | (Syn.IND_FAM_LINE (x, bx), arg0::args0, arg1::args1) =>
            let val true = Abt.eq (arg0, arg1)
            in EqIntroArgs' H meta (Var.Ctx.insert varenv x arg0) bx (args0, args1)
            end

    (* TODO order the subgoals according to the general guideline *)
    fun EqTyIntroArgs' H (meta as (opid, vlData, declArgs)) revTyArgs varenv decl conid ((args0, args1), args) =
      case (Syn.out decl, args0, args1, args) of
         (Syn.IND_FAM_BASE (l, constrs), _, _, []) =>
            let
              val (_, constr) = Option.valOf (List.find (fn (id, _) => id = conid) constrs)
            in
              EqIntroArgs' H (opid, vlData, (declArgs, List.rev revTyArgs)) varenv constr (args0, args1)
            end
       | (Syn.IND_FAM_FUN (a, x, bx), arg0::args0, arg1::args1, arg::args) =>
            (H >> AJ.EQ ((arg0, arg1), Abt.substVarenv varenv a))
            :: (H >> AJ.EQ ((arg0, arg), Abt.substVarenv varenv a))
            :: EqTyIntroArgs' H meta (arg::revTyArgs) (Var.Ctx.insert varenv x arg) bx conid ((args0, args1), args)
       | (Syn.IND_FAM_LINE (x, bx), arg0::args0, arg1::args1, arg::args) =>
            let
              val true = Abt.eq (arg0, arg1)
              val true = Abt.eq (arg0, arg)
            in
              EqTyIntroArgs' H meta (arg::revTyArgs) (Var.Ctx.insert varenv x arg) bx conid ((args0, args1), args)
            end
  in
    fun EqIntro H meta = EqTyIntroArgs' H meta [] Var.Ctx.empty
  end

  local
    fun elimSpecTerm meta constrs elimData (varenv as (recenv, renameenv)) term =
      case Syn.out term of
         Syn.VAR _ => Abt.substVarenv recenv (Abt.substVarenv renameenv term)
       | Syn.IND_SPEC_INTRO params => elimSpecIntro meta constrs elimData varenv params
       | Syn.IND_SPEC_FCOM params => elimSpecFcom meta constrs elimData varenv params
       | Syn.IND_SPEC_LAM (x,mx) => Syn.intoLam (x, elimSpecTerm meta constrs elimData varenv mx)
       | Syn.IND_SPEC_APP (m,n) => Syn.intoApp (elimSpecTerm meta constrs elimData varenv m, Abt.substVarenv renameenv n)

    and createVarenvForBranch meta constrs elimData (varenv as (_, renameenv)) acc (constr, vars, introArgs) =
      case (Syn.out constr, vars, introArgs) of
         (Syn.IND_CONSTR_DISCRETE _, [], []) => acc
       | (Syn.IND_CONSTR_KAN _, [], []) => acc
       | (Syn.IND_CONSTR_FUN (_,_,bx), var::vars, arg::introArgs) =>
            createVarenvForBranch meta constrs elimData varenv (Var.Ctx.insert acc var arg) (bx, vars, introArgs)
       | (Syn.IND_CONSTR_SPEC_FUN (a,_,bx), var::recvar::vars, arg::introArgs) =>
            let
              val acc = Var.Ctx.insert acc var (realizeSpecTerm meta renameenv arg)
              val acc = Var.Ctx.insert acc recvar (elimSpecTerm meta constrs elimData varenv arg)
            in
              createVarenvForBranch meta constrs elimData varenv acc (bx, vars, introArgs)
            end
       | _ => E.raiseError (E.IMPOSSIBLE (Fpp.text "createVarenv"))

    and elimSpecIntro meta constrs (elimData as (_, branches)) varenv (conid, introArgs) =
      let
        val (conIndex, (_, constr)) = Option.valOf (ListUtil.findIndex (fn (id, _) => id = conid) constrs)
        val Abt.\ (vars, branch) = List.nth (branches, conIndex)
      in
        Abt.substVarenv (createVarenvForBranch meta constrs elimData varenv Var.Ctx.empty (constr, vars, introArgs)) branch
      end

    and elimSpecFcom meta constrs (elimData as ((x,cx), branches)) (varenv as (_, renameenv)) {dir, cap, tubes} =
      let
        fun fcom y = realizeSpecFcom meta renameenv
          {dir = (#1 dir, y),
           cap = cap,
           tubes = tubes}
      in
        Syn.intoCom
          {dir = substSpan renameenv dir,
           ty = (x, Abt.substVarenv (Var.Ctx.insert renameenv x (fcom (VarKit.toDim x))) cx),
           cap = elimSpecTerm meta constrs elimData varenv cap,
           tubes = List.map (elimSpecTube meta constrs elimData varenv) tubes}
      end

    and elimSpecTube meta constrs elimData (varenv as (_, renameenv)) (eq, (u, term)) =
      (substSpan renameenv eq, (u, elimSpecTerm meta constrs elimData varenv term))

    fun elimSpecBoundary meta constrs elimData (varenv as (_, renameenv)) (eq, term) =
      (substSpan renameenv eq, elimSpecTerm meta constrs elimData varenv term)

    fun recResultType (motive as (x,cx)) varenv specTy arg =
      case Syn.out specTy of
         Syn.IND_SPECTYPE_SELF => Abt.substVar (arg, x) cx
       | Syn.IND_SPECTYPE_FUN (a,x,bx) =>
           Syn.into (Syn.FUN (Abt.substVarenv varenv a, x, recResultType motive varenv bx (Syn.intoApp (arg, VarKit.toExp x))))

    fun createVarenvsAndIntroArgs' H meta motive (recenv, varenv, varenv0, varenv1, revIntroArgs) (constr, vars0, vars1) =
      case (Syn.out constr, vars0, vars1) of
         (Syn.IND_CONSTR_DISCRETE boundaries, [], []) =>
           (H, varenv0, varenv1, List.rev revIntroArgs, (recenv, varenv, boundaries))
       | (Syn.IND_CONSTR_KAN boundaries, [], []) =>
           (H, varenv0, varenv1, List.rev revIntroArgs, (recenv, varenv, boundaries))
       | (Syn.IND_CONSTR_FUN (a,y,by), var0::vars0, var1::vars1) =>
           let
             val z = Sym.new ()
             val ztm = VarKit.toExp z
             val varenv' = Var.Ctx.insert varenv y ztm
             val varenv0' = Var.Ctx.insert varenv0 var0 ztm
             val varenv1' = Var.Ctx.insert varenv1 var1 ztm
           in
             createVarenvsAndIntroArgs' (H @> (z, AJ.TRUE (Abt.substVarenv varenv a)))
               meta motive (recenv, varenv', varenv0', varenv1', ztm :: revIntroArgs) (by, vars0, vars1)
           end
       | (Syn.IND_CONSTR_LINE (y,by), var0::vars0, var1::vars1) =>
           let
             val z = Sym.new ()
             val ztm = VarKit.toExp z
             val varenv' = Var.Ctx.insert varenv y ztm
             val varenv0' = Var.Ctx.insert varenv0 var0 ztm
             val varenv1' = Var.Ctx.insert varenv1 var1 ztm
           in
             createVarenvsAndIntroArgs' (H @> (z, AJ.TERM O.DIM))
               meta motive (recenv, varenv', varenv0', varenv1', ztm :: revIntroArgs) (by, vars0, vars1)
           end
       | (Syn.IND_CONSTR_SPEC_FUN (a,y,by), var0::recvar0::vars0, var1::recvar1::vars1) =>
           let
             val z = Sym.new ()
             val ztm = VarKit.toExp z
             val w = Sym.new ()
             val varenv' = Var.Ctx.insert varenv y ztm
             val varenv0' = Var.Ctx.insert varenv0 var0 ztm
             val varenv1' = Var.Ctx.insert varenv1 var1 ztm
             val recenv = Var.Ctx.insert recenv z (VarKit.toExp w)
           in
             createVarenvsAndIntroArgs'
               (H @> (z, AJ.TRUE (realizeSpecType meta varenv a))
                  @> (w, AJ.TRUE (recResultType motive varenv a ztm)))
               meta motive (recenv, varenv', varenv0', varenv1', ztm :: revIntroArgs) (by, vars0, vars1)
           end

    fun createVarenvsAndIntroArgs H meta motive =
      createVarenvsAndIntroArgs' H meta motive
        (Var.Ctx.empty, Var.Ctx.empty, Var.Ctx.empty, Var.Ctx.empty, [])

    fun restrictedEq eqs H params =
      case Restriction.restrict eqs of
         SOME f => [Sequent.map f (H >> AJ.EQ params)]
       | NONE => []

    fun restrictedEqIfDifferent eqs H (params as ((tm0, tm1), ty)) =
      if Abt.eq (tm0, tm1) then [] else restrictedEq eqs H params
  in
    fun EqElimBranches H meta (motive as (x,cx)) constrs (branches0, branches1) =
      let
        val (goalBranches, goalCoh) = ListPair.unzip @@ ListPair.mapEq
          (fn ((conid, constr), (Abt.\ (vars0, branch0), Abt.\ (vars1, branch1))) =>
            let
              val (H, varenv0, varenv1, introArgs, (recenv, varenv, boundaries)) =
                createVarenvsAndIntroArgs H meta motive (constr, vars0, vars1)
              val cintro = Abt.substVar (realizeSpecIntro meta Var.Ctx.empty (conid, introArgs), x) cx
              val branch0 = Abt.substVarenv varenv0 branch0
              val branch1 = Abt.substVarenv varenv0 branch1
              val goalBranch = H >> AJ.EQ ((branch0, branch1), cintro)
              val goalCohs = ListUtil.concatMap
                (fn boundary =>
                  let
                    val (eq, term) = elimSpecBoundary meta constrs (motive, branches0) (recenv, varenv) boundary
                  in
                    restrictedEq [eq] H ((branch0, term), cintro)
                  end)
                boundaries
            in
              (goalBranch, goalCohs)
            end)
          (constrs, ListPair.zipEq (branches0, branches1))
      in
        goalBranches @ List.concat goalCoh
      end
  end


end
