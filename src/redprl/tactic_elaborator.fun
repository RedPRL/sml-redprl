functor TacticElaborator (Sig : MINI_SIGNATURE) :
sig
  type sign = Sig.sign
  type script = RedPrlAbt.abt

  type tactic = Lcf.jdg Lcf.tactic
  type multitactic = Lcf.jdg Lcf.multitactic

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
  type tactic = Lcf.jdg Lcf.tactic
  type multitactic = Lcf.jdg Lcf.multitactic

  structure R = Refiner (Sig)
  structure RT = RefinerTypeRules (Sig)
  structure T = RedPrlTactical (Lcf)

  open T infix seq then_ thenl thenl' orelse_ par

  type env = multitactic Var.Ctx.dict

  fun ?e = raise e
  exception todo

  open Tm infix $ $$ $# \
  structure O = RedPrlOpData

  fun hole (pos : Pos.t, name : string option) : multitactic = 
    fn state =>
      let
        val header = Fpp.seq [Fpp.text (Option.getOpt (name, "")), Fpp.char #"."]
        val message = Fpp.vsep [header, Lcf.prettyState state]
      in
        RedPrlLog.print RedPrlLog.INFO (SOME pos, message);
        Lcf.all Lcf.idn state
      end

  fun fail msg = 
    fn state => 
      RedPrlError.raiseError (RedPrlError.GENERIC [Fpp.text msg])

  fun @@ (f, x) = f x
  infixr @@

  fun complete tac = 
    tac then_ fail "incomplete"

  fun autoTac sign = repeat (try @@ R.AutoStep sign)
  fun autoTacComplete sign = try (complete (autoTac sign) orelse_ R.NondetStepJdgFromHyp)

  fun exactAuto sign m = 
    R.Exact m thenl [autoTacComplete sign]

  fun pushNames xs = 
    Lcf.rule (R.Names.Push xs)

  fun popNamesIn xs tac = 
    Lcf.rule (R.Names.PopAs xs)
      then_ tac
      then_ pushNames xs

  fun popSpecificNamesIn xs tac = 
    Lcf.rule (R.Names.PopSpecific xs )
      then_ tac
      then_ pushNames xs

  fun hyp sign z =
    Lcf.rule (R.Hyp.Project z)
    par
    exactAuto sign (VarKit.toExp z)

  open Sequent infix >>
  structure AJ = AtomicJudgment and Syn = SyntaxView

  fun elimRule sign z tacs = 
    R.Elim sign z thenl tacs

  local
    fun recordElimBasis (lbls, names) tac ty z =
      let
        val Syn.RECORD fields = Syn.out ty
        val nameMap = ListPair.zipEq (lbls, names)

        fun nameForLabel lbl =
          SOME @@ Syn.Fields.lookup lbl nameMap
          handle Syn.Fields.Absent => NONE

        val (xs, xs') =
          List.foldl
            (fn (((lbl, _), _), (xs, xs')) =>
             case nameForLabel lbl of 
                SOME x => (x::xs, xs')
              | NONE => 
                let
                  val x = Sym.named lbl
                in
                  (x::xs, x :: xs')
                end)
            ([],[])
            fields
      in
        Lcf.rule (RT.Record.Elim z) thenl [popNamesIn xs (pushNames xs' then_ tac)]
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
    T.try (Lcf.rule (R.Hyp.Delete name))

  fun decomposeStitched sign z (pattern : Sym.t O.dev_pattern) tac = 
    case pattern of 
        O.PAT_VAR u => 
        pushNames [z] thenl [popNamesIn [u] tac]

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

  fun applications sign z (pattern, names) tacs tac =
    let
      val n = List.length tacs
      val z' = Sym.new ()
      val p = Sym.named "_"
    in
      if n = 0 then 
        decompose sign z (pattern, names) tac
      else
        Lcf.rule (RT.MultiArrow.Elim sign (List.length tacs) z) thenl
          (tacs @ [popNamesIn [p, z'] @@ decompose sign z' (pattern, names) tac])
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
        Lcf.rule RT.Record.True thenl fieldTactics @ famTactics
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
        Lcf.rule RT.Fun.True thenl [popNamesIn [name] continue, autoTacComplete sign]
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
      Lcf.rule RT.Line.True
        thenl [popNamesIn [u] (pathIntros sign us tac)]

    and pathIntrosBasis sign (u, us) tac _ =
      Lcf.rule RT.Path.True
        thenl [popNamesIn [u] (pathIntros sign us tac), autoTacComplete sign, autoTacComplete sign]

    and pathIntros sign us tac =
      case us of
         [] => tac
       | u :: us =>
           R.Tactical.NormalizeGoalDelegate
             (fn tm => pathIntrosBasis sign (u, us) tac tm orelse_ lineIntrosBasis sign (u, us) tac tm)
             sign
  in
    val pathIntros = pathIntros
  end

  fun cutLemma sign cust (pattern, names) appTacs tac =
    let
      val z = RedPrlSym.new ()
      val continue = applications sign z (pattern, names) appTacs tac
    in
      Lcf.rule (R.CutLemma sign cust) thenl [popNamesIn [z] continue]
    end
    
  fun onAllHyps tac (H >> jdg) =
    (Hyps.foldl (fn (x, _, tac') => tac x thenl [tac']) T.idn H) (H >> jdg)

  val inversions = onAllHyps (T.try o R.Inversion)

  fun addPosition tm exn = 
    let
      val pos = Tm.getAnnotation tm
    in
      RedPrlError.addPosition (pos, exn)
    end

  fun tactic sign env tm jdg = 
    Lcf.M.mapErr
      (addPosition tm)
      (tactic_ sign env tm jdg)

  and multitactic sign env tm jdg = 
    Lcf.M.mapErr
      (addPosition tm)
      (multitactic_ sign env tm jdg)

  and tactic_ sign env tm = 
    case Tm.out tm of 
       O.TAC_MTAC $ [_ \ tm] => multitacToTac (multitactic sign env tm)
     | O.TAC_ID $ _ => idn
     | O.TAC_AUTO_STEP $ _ => R.AutoStep sign
     | O.TAC_ELIM $ [_ \ any] => R.Elim sign (VarKit.fromTerm (Syn.unpackAny any))
     | O.TAC_REWRITE $ [_ \ sel, _ \ acc, _ \ tm] => R.Rewrite sign (Syn.outSelector sel, Syn.outAccessor acc) tm thenl [autoTacComplete sign, autoTacComplete sign, autoTacComplete sign, autoTacComplete sign]
     | O.RULE_EXACT $ [_ \ any] => R.Exact (Syn.unpackAny any)
     | O.TAC_SYMMETRY $ _ => R.Symmetry
     | O.DEV_INVERSION $ _ => inversions
     | O.RULE_CUT $ [_ \ catjdg] => Lcf.rule (R.Cut (AJ.out catjdg))
     | O.TAC_REDUCE_ALL $ _ => R.Computation.ReduceAll sign
     | O.TAC_REDUCE $ [_ \ sels] => Lcf.rule (R.Computation.Reduce sign (Syn.outVec' Syn.outSelector sels))
     | O.TAC_REDUCE_PART $ [_ \ sel, _ \ accs] => Lcf.rule (R.Computation.ReducePart sign (Syn.outSelector sel, Syn.outVec' Syn.outAccessor accs))
     | O.TAC_UNFOLD_ALL opids $ _ => Lcf.rule (R.Custom.UnfoldAll sign opids)
     | O.TAC_UNFOLD opids $ [_ \ vec] => Lcf.rule (R.Custom.Unfold sign opids (Syn.outVec' Syn.outSelector vec))
     | O.TAC_ASSUMPTION $ _ => R.NondetStepJdgFromHyp
     | O.RULE_PRIM ruleName $ _ => R.lookupRule sign ruleName
     | O.DEV_LET _ $ [_ \ jdg, _ \ tm1, [u] \ tm2] => Lcf.rule (R.Cut (AJ.out jdg)) thenl [tactic sign env tm1, popNamesIn [u] @@ tactic sign env tm2]
     | O.DEV_FUN_INTRO pats $ [us \ tm] => funIntros sign (pats, us) (tactic sign env tm)
     | O.DEV_RECORD_INTRO lbls $ args => recordIntro sign lbls (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.DEV_PATH_INTRO _ $ [us \ tm] => pathIntros sign us (tactic sign env tm)
     | O.DEV_BOOL_ELIM $ [_ \ var, _ \ tm1, _ \ tm2] => elimRule sign (VarKit.fromTerm var) [tactic sign env tm1, tactic sign env tm2, autoTacComplete sign, autoTacComplete sign]
     | O.DEV_S1_ELIM $ [_ \ var, _ \ tm1, [v] \ tm2] => elimRule sign (VarKit.fromTerm var) [tactic sign env tm1, popNamesIn [v] (tactic sign env tm2), autoTacComplete sign, autoTacComplete sign, autoTacComplete sign]
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
         applications sign z (O.PAT_VAR (), [z']) tacs (hyp sign z')
       end

     | O.DEV_APPLY_LEMMA pat $ [_ \ any, _ \ tacVec, names \ tac] =>
       let
         val cust = Syn.unpackAny any
         val O.MK_VEC _ $ appArgs = Tm.out tacVec
         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs         
         val tac = tactic sign env tac         
       in
         cutLemma sign cust (pat, names) appTacs tac
       end

     | O.DEV_USE_LEMMA $ [_ \ any, _ \ tacVec] =>
       let
         val cust = Syn.unpackAny any
         val O.MK_VEC _ $ appArgs = Tm.out tacVec
         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
         val z = RedPrlSym.new ()
       in
         cutLemma sign cust (O.PAT_VAR (), [z]) appTacs (hyp sign z)
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

         fun reviveClause (pvars \ clause) jdg =
           let
             val O.DEV_MATCH_CLAUSE $ [_ \ pat, _ \ handler] = out clause
             val metas = Unify.Metas.fromList pvars
             val pat' = defrostMetas metas (Syn.unpackAny pat)
             val handler' = defrostMetas metas handler
             val rho = Unify.unify metas (Syn.unpackAny term, pat')
             val handler'' = substMetaenv rho handler'
           in
             tactic sign env handler'' jdg
           end

         fun fail _ = Lcf.M.throw (RedPrlError.errorToExn (Tm.getAnnotation tm, RedPrlError.GENERIC [Fpp.text "No matching clause"]))
       in
         List.foldr (fn (clause, tac) => T.orelse_ (reviveClause clause, tac)) fail clauses
       end
     | O.DEV_QUERY $ [_ \ selTm, [x] \ tm] =>
       (fn jdg as H >> concl =>
         let
           val sel = Syn.outSelector selTm
           val atjdg = Sequent.lookupSelector sel (H, concl)
           val tm' = substVar (AJ.into atjdg, x) tm
         in
           tactic sign env tm' jdg
         end)
     | O.DEV_PRINT $ [_ \ tm'] =>
       (RedPrlLog.print RedPrlLog.INFO (getAnnotation tm, TermPrinter.ppTerm tm');
        T.idn)
     | O.TAC_FAIL $ _ => fail "fail"
     | O.TAC_POP _ $ [xs \ tm] =>
       popNamesIn xs (tactic sign env tm)
     | O.TAC_PUSH $ [_ \ vec] => 
       let
         val xs = Syn.outVec' (VarKit.fromTerm o Syn.unpackAny) vec
       in
         Lcf.rule (R.Names.Push xs)
       end
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized tactic", TermPrinter.ppTerm tm]

  and multitactic_ sign env tm =
    case Tm.out tm of 
       O.MTAC_ALL $ [_ \ tm] => T.all (tactic sign env tm)
     | O.MTAC_EACH $ [_ \ vec] => T.each (Syn.outVec' (tactic sign env) vec)
     | O.MTAC_FOCUS i $ [_ \ tm] => T.only (i, tactic sign env tm)
     | O.MTAC_PROGRESS $ [_ \ tm] => T.mprogress (multitactic sign env tm)
     | O.MTAC_SEQ $ [_ \ tm1, _ \ tm2] => T.seq (multitactic sign env tm1, multitactic sign env tm2)
     | O.MTAC_ORELSE $ [_ \ tm1, _ \ tm2] => T.morelse (multitactic sign env tm1, multitactic sign env tm2)
     | O.MTAC_HOLE msg $ _ => hole (Option.valOf (Tm.getAnnotation tm), msg)
     | O.MTAC_REPEAT $ [_ \ tm] => T.mrepeat (multitactic sign env tm)
     | O.MTAC_AUTO $ _ => all (autoTac sign)
     | O.CUST (opid, _) $ args => multitactic sign env (Sig.unfoldOpid sign opid args)
     | `x => Var.Ctx.lookup env x
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized multitactic", TermPrinter.ppTerm tm]

end
