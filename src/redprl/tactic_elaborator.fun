functor TacticElaborator (Sig : MINI_SIGNATURE) :
sig
  type sign = Sig.sign
  type script = RedPrlAbt.abt

  type 'a nominal = (int -> Sym.t) -> 'a
  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal

  type env = multitactic Var.Ctx.dict

  val tactic : sign -> env -> script -> tactic
  val multitactic : sign -> env -> script -> multitactic
end = 
struct

  (* HINT: raise exceptions for fatal internal/implementation errors; but use Lcf.M.throw for user errors. *)

  structure Tm = RedPrlAbt
  structure Unify = AbtUnify (RedPrlAbt)
  structure Syn = SyntaxView

  type sign = Sig.sign
  type script = Tm.abt
  type 'a nominal = (int -> Sym.t) -> 'a
  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal

  structure R = Refiner (Sig)
  structure RT = RefinerTypeRules (Sig)
  structure T = RedPrlTactical (Lcf)

  open T infix seq then_ thenl thenl' orelse_

  type env = multitactic Var.Ctx.dict

  fun ?e = raise e
  exception todo

  open Tm infix $ $$ $# \
  structure O = RedPrlOpData

  fun hole (pos : Pos.t, name : string option) : multitactic = 
    fn alpha => fn state =>
      let
        val header = Fpp.seq [Fpp.text (Option.getOpt (name, "hole")), Fpp.char #"."]
        val message = Fpp.vsep [header, Lcf.prettyState state]
      in
        RedPrlLog.print RedPrlLog.INFO (SOME pos, message);
        Lcf.all Lcf.idn state
      end

  fun fail msg = 
    fn alpha => fn state => 
      RedPrlError.raiseError (RedPrlError.GENERIC [Fpp.text msg])

  fun hyp z =
    Lcf.rule o R.Hyp.Project z
    orelse_
      R.SynthFromHyp z

  open Sequent infix >>
  structure AJ = AtomicJudgment and Syn = SyntaxView

  val autoMtac = mrepeat o all o try o R.AutoStep
  val autoTac = multitacToTac o autoMtac
  fun autoTacComplete sign = try (autoTac sign then_ fail "'auto' failed to discharge this auxiliary goal")

  fun elimRule sign z xs tacs = 
    R.Elim sign z thenl' (xs, tacs)

  local
    fun recordElimBasis (lbls, names) tac ty z =
      let
        val Syn.RECORD fields = Syn.out ty
        val nameMap = ListPair.zipEq (lbls, names)
        fun nameForLabel lbl =
          Syn.Fields.lookup lbl nameMap
          handle Syn.Fields.Absent => Sym.named ("@" ^ lbl)
        val xs = List.map (fn ((lbl, _), _) => nameForLabel lbl) fields
      in
        Lcf.rule o RT.Record.Elim z thenl' (xs, [tac])
      end
  in
    fun recordElim (lbls, names) tac =
      R.Tactical.NormalizeHypDelegate
        (recordElimBasis (lbls, names) tac)
  end

  fun stitchPattern (pattern : unit O.dev_pattern, names : Sym.t list) : Sym.t O.dev_pattern * Sym.t list =
    let
      fun go (O.PAT_VAR (), u :: names) = (O.PAT_VAR u, names)
        | go (O.PAT_TUPLE lpats, names) =
          let
            val (lpats', names') = goTuple (lpats, names)
          in
            (O.PAT_TUPLE lpats', names')
          end
      and goTuple ([], names) = ([], names)
        | goTuple ((lbl, pat) :: lpats, names) =
          let
            val (pat', names') = go (pat, names)
            val (lpats', names'') = goTuple (lpats, names')
          in
            ((lbl, pat') :: lpats', names'')
          end
    in
      go (pattern, names)
    end
    handle _ => 
      raise RedPrlError.error [Fpp.text "stitchPattern encountered mismatch!"]

  (* R.Hyp.Delete can fail if the hypothesis is mentioned. *)
  fun deleteHyp name = 
    T.try (Lcf.rule o R.Hyp.Delete name)

  fun decomposeStitched sign z (pattern : Sym.t O.dev_pattern) tac = 
    case pattern of 
        O.PAT_VAR u => Lcf.rule o (R.Hyp.Rename z) thenl' ([u], [tac])
      | O.PAT_TUPLE labeledPatterns =>
        let
          val (lbls, pats) = ListPair.unzip labeledPatterns
          val names = List.map (fn lbl => Sym.named ("tmp/" ^ lbl)) lbls

          val rec go = 
            fn [] => tac
            | (name, pat) :: rest => decomposeStitched sign name pat (deleteHyp name thenl [go rest])

          val continue = go (ListPair.zip (names, pats))
        in
          recordElim (lbls, names) continue sign z
        end

  fun decompose sign z =
    decomposeStitched sign z
      o #1
      o stitchPattern

  fun apply sign z names (appTac, contTac) alpha jdg = 
    let
      val H >> _ = jdg
      val AJ.TRUE ty = RT.Hyps.lookup H z
    in
      case Syn.out ty of 
         Syn.FUN _ => (Lcf.rule o RT.Fun.Elim z thenl' (names, [appTac, contTac])) alpha jdg
       | Syn.PATH _ => (Lcf.rule o RT.Path.Elim z thenl' (names, [appTac, contTac])) alpha jdg
       | Syn.LINE _ => (Lcf.rule o RT.Line.Elim z thenl' (names, [appTac, contTac])) alpha jdg
       | _ => raise RedPrlError.error [Fpp.text "'apply' tactical does not apply"]
    end

  fun applications sign z (pattern, names) tacs tac =
    case tacs of 
       [] => decompose sign z (pattern, names) tac
     | appTac :: tacs =>
       let
         val z' = Sym.named (Sym.toString z ^ "'")
         val p = Sym.named "_"
       in
         apply sign z [z',p] (appTac, applications sign z' (pattern, names) tacs tac)
       end

  local
    fun recordIntroBasis sign lbls tacs ty =
      let
        val Syn.RECORD fields = Syn.out ty

        val labeledTactics = ListPair.zipEq (lbls, tacs)

        fun tacticForLabel lbl =
          case ListUtil.findIndex (fn (lbl', _) => lbl = lbl') labeledTactics of
             SOME (_, (_, tac)) => tac
           | NONE => idn

        val fieldTactics = List.map (fn ((lbl, _), _) => tacticForLabel lbl) fields
        val famTactics = List.tabulate (List.length fields - 1, fn _ => autoTacComplete sign)
      in
        Lcf.rule o RT.Record.True thenl fieldTactics @ famTactics
      end
  in
    fun recordIntro sign lbls tacs =
      R.Tactical.NormalizeGoalDelegate
        (recordIntroBasis sign lbls tacs) sign
  end


  fun nameForPattern pat = 
    case pat of 
       O.PAT_VAR x => x
     | O.PAT_TUPLE lpats => Sym.named (ListUtil.joinWith (Sym.toString o nameForPattern o #2) "-" lpats)

  local
    fun funIntrosBasis sign (pat, pats, names) tac _ =
      let
        val (pat', names') = stitchPattern (pat, names)
        val name = nameForPattern pat'
        val intros = funIntros sign (pats, names') tac
        val continue =
          case pat' of
             O.PAT_VAR _ => intros
           | _ => decomposeStitched sign name pat' (deleteHyp name thenl [intros])
      in
        Lcf.rule o RT.Fun.True thenl' ([name], [continue, autoTacComplete sign])
      end

    and funIntros sign (pats, names) tac =
      case pats of
         [] => tac
       | pat :: pats =>
           R.Tactical.NormalizeGoalDelegate
             (funIntrosBasis sign (pat, pats, names) tac) sign
  in
    val funIntros = funIntros
  end

  local
    fun lineIntrosBasis sign (u, us) tac _ = 
      Lcf.rule o RT.Line.True
        thenl' ([u], [pathIntros sign us tac])

    and pathIntrosBasis sign (u, us) tac _ =
      Lcf.rule o RT.Path.True
        thenl' ([u], [pathIntros sign us tac, autoTacComplete sign, autoTacComplete sign])

    and pathIntros sign us tac =
      case us of
         [] => tac
       | u :: us =>
           R.Tactical.NormalizeGoalDelegate
             (fn alpha => pathIntrosBasis sign (u, us) tac alpha orelse_ lineIntrosBasis sign (u, us) tac alpha)
             sign
  in
    val pathIntros = pathIntros
  end

  fun exactAuto sign m = 
    R.Exact m thenl [autoTacComplete sign]

  fun cutLemma sign opid ar (args : abt bview list) (pattern, names) appTacs tac =
    let
      val (vls, _) = ar
      fun processArg (xs \ m, (taus, _), {subtermNames, subtermTacs}) =
        {subtermNames = xs @ subtermNames,
         subtermTacs = exactAuto sign m :: subtermTacs}

      val {subtermNames, subtermTacs} =
        ListPair.foldr processArg {subtermNames = [], subtermTacs = []} (args, vls)

      val z = RedPrlSym.new ()
      val continue = applications sign z (pattern, names) appTacs tac
    in
      Lcf.rule o R.CutLemma sign opid thenl' (z :: subtermNames, subtermTacs @ [continue])
    end
    
  fun onAllHyps tac alpha (H >> jdg) =
    (SequentData.Hyps.foldl (fn (x, _, tac') => tac x thenl [tac']) T.idn H) alpha (H >> jdg)

  val inversions = onAllHyps (T.try o R.Inversion)

  fun addPosition tm exn = 
    let
      val pos = Tm.getAnnotation tm
    in
      RedPrlError.addPosition (pos, exn)
    end

  fun tactic sign env tm alpha jdg = 
    Lcf.M.mapErr
      (addPosition tm)
      (tactic_ sign env tm alpha jdg)

  and multitactic sign env tm alpha jdg = 
    Lcf.M.mapErr
      (addPosition tm)
      (multitactic_ sign env tm alpha jdg)

  and tactic_ sign env tm = 
    case Tm.out tm of 
       O.TAC_MTAC $ [_ \ tm] => multitacToTac (multitactic sign env tm)
     | O.TAC_ID $ _ => idn
     | O.TAC_AUTO_STEP $ _ => R.AutoStep sign
     | O.TAC_ELIM $ [_ \ any] => R.Elim sign (VarKit.fromTerm (Syn.unpackAny any))
     | O.TAC_REWRITE $ [_ \ sel, _ \ acc, _ \ tm] => R.Rewrite sign (Syn.outSelector sel, Syn.outAccessor acc) tm thenl' ([], [autoTacComplete sign, autoTacComplete sign, autoTacComplete sign, autoTacComplete sign])
     | O.TAC_REWRITE_HYP $ [_ \ sel, _ \ any] => R.RewriteHyp sign (Syn.outSelector sel) (VarKit.fromTerm (Syn.unpackAny any))
     | O.RULE_EXACT $ [_ \ any] => R.Exact (Syn.unpackAny any)
     | O.TAC_SYMMETRY $ _ => R.Symmetry
     | O.DEV_INVERSION $ _ => inversions
     | O.RULE_CUT $ [_ \ catjdg] => Lcf.rule o R.Cut (AJ.out catjdg)
     | O.TAC_REDUCE_ALL $ _ => R.Computation.ReduceAll sign
     | O.TAC_REDUCE $ [_ \ sels] => Lcf.rule o R.Computation.Reduce sign (Syn.outVec' Syn.outSelector sels)
     | O.TAC_UNFOLD_ALL opids $ _ => Lcf.rule o R.Custom.UnfoldAll sign opids
     | O.TAC_UNFOLD opids $ [_ \ vec] => Lcf.rule o R.Custom.Unfold sign opids (Syn.outVec' Syn.outSelector vec)
     | O.RULE_PRIM ruleName $ _ => R.lookupRule ruleName
     | O.DEV_LET _ $ [_ \ jdg, _ \ tm1, [u] \ tm2] => Lcf.rule o R.Cut (AJ.out jdg) thenl' ([u], [tactic sign env tm1, tactic sign env tm2])
     | O.DEV_FUN_INTRO pats $ [us \ tm] => funIntros sign (pats, us) (tactic sign env tm)
     | O.DEV_RECORD_INTRO lbls $ args => recordIntro sign lbls (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.DEV_PATH_INTRO _ $ [us \ tm] => pathIntros sign us (tactic sign env tm)
     | O.DEV_BOOL_ELIM $ [_ \ var, _ \ tm1, _ \ tm2] => elimRule sign (VarKit.fromTerm var) [] [tactic sign env tm1, tactic sign env tm2]
     | O.DEV_S1_ELIM $ [_ \ var, _ \ tm1, [v] \ tm2] => elimRule sign (VarKit.fromTerm var) [v] [tactic sign env tm1, tactic sign env tm2, autoTacComplete sign, autoTacComplete sign, autoTacComplete sign]
     | O.DEV_APPLY_HYP pattern $ [_ \ var, _ \ vec, names \ tm'] =>
       let
         val z = VarKit.fromTerm (Syn.unpackAny var)
         val tacs = Syn.outVec' (tactic sign env) vec
         val tac = tactic sign env tm'
       in
         applications sign z (pattern, names) tacs tac
       end
     | O.DEV_USE_HYP $ [_ \ var, _ \ vec] => 
       let
         val z = VarKit.fromTerm (Syn.unpackAny var)
         val tacs = Syn.outVec' (tactic sign env) vec
         val z' = RedPrlSym.named (Sym.toString z ^ "'")
       in
         applications sign z (O.PAT_VAR (), [z']) tacs (hyp z')
       end

     | O.DEV_APPLY_LEMMA (opid, ar, pat) $ args =>
       let
         val (names \ tac) :: (_ \ vec) :: revSubtermArgs = List.rev args
         val subtermArgs = List.rev revSubtermArgs
         val O.MK_VEC _ $ appArgs = Tm.out vec

         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
         val tac = tactic sign env tac
       in
         cutLemma sign opid (Option.valOf ar) subtermArgs (pat, names) appTacs tac
       end
     | O.DEV_USE_LEMMA (opid, ar) $ args =>
       let
         val (_ \ vec) :: revSubtermArgs = List.rev args
         val subtermArgs = List.rev revSubtermArgs
         val O.MK_VEC _ $ appArgs = Tm.out vec

         val z = RedPrlSym.named (opid ^ "'")
         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
       in
         cutLemma sign opid (Option.valOf ar) subtermArgs (O.PAT_VAR (), [z]) appTacs (hyp z)
       end
     | O.CUST (opid, _) $ args => tactic sign env (Sig.unfoldOpid sign opid args)
     | O.DEV_MATCH ns $ (_ \ term) :: clauses =>
       let
         fun defrostMetas metas =
           let
             fun go tm = 
               case out tm of
                  O.PAT_META tau $ [_ \ meta, _ \ vec] =>
                  let
                    val x = VarKit.fromTerm meta
                    val args = Syn.outVec' Syn.unpackAny vec
                  in
                    if Unify.Metas.member metas x then 
                     check (x $# args, tau)
                    else
                      tm 
                  end
                | _ => tm
           in
             go o deepMapSubterms go
           end

         fun reviveClause (pvars \ clause) alpha jdg =
           let
             val O.DEV_MATCH_CLAUSE $ [_ \ pat, _ \ handler] = out clause
             val metas = Unify.Metas.fromList pvars
             val pat' = defrostMetas metas (Syn.unpackAny pat)
             val handler' = defrostMetas metas handler
             val rho = Unify.unify metas (Syn.unpackAny term, pat')
             val handler'' = substMetaenv rho handler'
           in
             tactic sign env handler'' alpha jdg
           end

         fun fail _ _ = Lcf.M.throw (RedPrlError.errorToExn (Tm.getAnnotation tm, RedPrlError.GENERIC [Fpp.text "No matching clause"]))
       in
         List.foldr (fn (clause, tac) => T.orelse_ (reviveClause clause, tac)) fail clauses
       end
     | O.DEV_QUERY $ [_ \ selTm, [x] \ tm] =>
       (fn alpha => fn jdg as H >> concl =>
         let
           val sel = Syn.outSelector selTm
           val atjdg = Sequent.lookupSelector sel (H, concl)
           val tm' = substVar (AJ.into atjdg, x) tm
         in
           tactic sign env tm' alpha jdg
         end)
     | O.DEV_PRINT $ [_ \ tm'] =>
       (RedPrlLog.print RedPrlLog.INFO (getAnnotation tm, TermPrinter.ppTerm tm');
        T.idn)
     | O.TAC_FAIL $ _ => fail "fail"
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized tactic", TermPrinter.ppTerm tm]

  and multitactic_ sign env tm =
    case Tm.out tm of 
       O.MTAC_ALL $ [_ \ tm] => T.all (tactic sign env tm)
     | O.MTAC_EACH $ [_ \ vec] => T.each (Syn.outVec' (tactic sign env) vec)
     | O.MTAC_FOCUS i $ [_ \ tm] => T.only (i, tactic sign env tm)
     | O.MTAC_PROGRESS $ [_ \ tm] => T.mprogress (multitactic sign env tm)
     | O.MTAC_REC $ [[x] \ tm] => T.mrec (fn mt => multitactic sign (Var.Ctx.insert env x mt) tm)
     | O.MTAC_SEQ _ $ [_ \ tm1, us \ tm2] => T.seq (multitactic sign env tm1, (us, multitactic sign env tm2))
     | O.MTAC_ORELSE $ [_ \ tm1, _ \ tm2] => T.morelse (multitactic sign env tm1, multitactic sign env tm2)
     | O.MTAC_HOLE msg $ _ => hole (Option.valOf (Tm.getAnnotation tm), msg)
     | O.MTAC_REPEAT $ [_ \ tm] => T.mrepeat (multitactic sign env tm)
     | O.MTAC_AUTO $ _ => autoMtac sign
     | O.CUST (opid, _) $ args => multitactic sign env (Sig.unfoldOpid sign opid args)
     | `x => Var.Ctx.lookup env x
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized multitactic", TermPrinter.ppTerm tm]

end
