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
  structure Tm = RedPrlAbt
  structure Unify = AbtUnify (RedPrlAbt)

  type sign = Sig.sign
  type script = Tm.abt
  type 'a nominal = (int -> Sym.t) -> 'a
  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal

  structure R = Refiner (Sig)
  structure RT = RefinerTypeRules (Sig)
  structure T = RedPrlTactical (Lcf)

  open T infix seq then_ thenl thenl'

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

  fun hyp z alpha jdg =
    R.Hyp.Project z alpha jdg
    handle exn =>
      R.SynthFromHyp z alpha jdg
      handle _ => raise exn

  open RedPrlSequent infix >>
  structure AJ = RedPrlAtomicJudgment and Syn = Syntax

  val autoMtac = mrepeat o all o try o R.AutoStep
  val autoTac = multitacToTac o autoMtac

  fun unfoldCustomOperator sign (opid, args) = 
    Sig.unfoldCustomOperator (Sig.lookup sign opid) args

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
        RT.Record.Elim z thenl' (xs, [tac])
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
    T.try (R.Hyp.Delete name)

  fun decomposeStitched sign z (pattern : Sym.t O.dev_pattern) tac = 
    case pattern of 
        O.PAT_VAR u => R.Hyp.Rename z thenl' ([u], [tac])
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
      val AJ.TRUE (ty, _, _) = RT.Hyps.lookup z H
    in
      case Syn.out ty of 
         Syn.FUN _ => (RT.Fun.Elim z thenl' (names, [appTac, contTac])) alpha jdg
       | Syn.PATH_TY _ => (RT.Path.Elim z thenl' (names, [appTac, contTac])) alpha jdg
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
        val famTactics = List.tabulate (List.length fields - 1, fn _ => autoTac sign)
      in
        RT.Record.True thenl fieldTactics @ famTactics
      end
  in
    fun recordIntro sign lbls tacs =
      R.Tactical.NormalizeGoalDelegate
        (recordIntroBasis sign lbls tacs) sign
  end


  fun nameForPattern pat = 
    case pat of 
       O.PAT_VAR x => x
     | O.PAT_TUPLE lpats => Sym.named (ListSpine.pretty (Sym.toString o nameForPattern o #2) "-" lpats)

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
        RT.Fun.True thenl' ([name], [continue, autoTac sign])
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
    fun pathIntrosBasis sign (u, us) tac _ =
      RT.Path.True thenl' ([u], [pathIntros sign us tac, autoTac sign, autoTac sign])

    and pathIntros sign us tac =
      case us of
         [] => tac
       | u :: us =>
           R.Tactical.NormalizeGoalDelegate
             (pathIntrosBasis sign (u, us) tac) sign
  in
    val pathIntros = pathIntros
  end

  fun exactAuto sign m = 
    R.Exact m thenl [autoTac sign]

  fun cutLemma sign opid ar (args : abt bview list) (pattern, names) appTacs tac =
    let
      val (vls, _) = ar
      fun processArg ((us, xs) \ m, ((sigmas, taus), _), {subtermNames, subtermTacs}) =
        let
          val syms = ListPair.zipEq (us, sigmas)
        in
          {subtermNames = us @ xs @ subtermNames,
           subtermTacs = exactAuto sign m :: subtermTacs}
        end

      val {subtermNames, subtermTacs} = ListPair.foldr processArg {subtermNames = [], subtermTacs = []} (args, vls)

      val z = RedPrlSym.new ()
      val continue = applications sign z (pattern, names) appTacs tac
    in
      R.CutLemma sign opid thenl' (z :: subtermNames, subtermTacs @ [continue])
    end

  fun tactic sign env tm alpha jdg = 
    RedPrlError.annotateException' (Tm.getAnnotation tm)
      (fn _ => tactic_ sign env tm alpha jdg)

  and multitactic sign env tm alpha jdg = 
    RedPrlError.annotateException' (Tm.getAnnotation tm)
      (fn _ => multitactic_ sign env tm alpha jdg)

  and tactic_ sign env tm = 
    case Tm.out tm of 
       O.MONO O.TAC_MTAC $ [_ \ tm] => multitacToTac (multitactic sign env tm)
     | O.MONO O.RULE_ID $ _ => idn
     | O.MONO O.RULE_AUTO_STEP $ _ => R.AutoStep sign
     | O.MONO (O.RULE_ELIM _) $ [_ \ z] => R.Elim sign (VarKit.fromTerm z)
     | O.MONO O.RULE_REWRITE $ [_ \ sel, _ \ tm] => R.Rewrite sign (Syn.outSelector sel) tm thenl' ([], [autoTac sign, autoTac sign, autoTac sign, autoTac sign])
     | O.MONO O.RULE_REWRITE_HYP $ [_ \ sel, _ \ var] => R.RewriteHyp sign (Syntax.outSelector sel) (VarKit.fromTerm var)
     | O.MONO (O.RULE_EXACT _) $ [_ \ tm] => R.Exact tm
     | O.MONO O.RULE_SYMMETRY $ _ => R.Symmetry
     | O.MONO O.RULE_CUT $ [_ \ catjdg] => R.Cut (AJ.out catjdg)
     | O.MONO O.RULE_REDUCE_ALL $ _ => R.Computation.ReduceAll sign
     | O.MONO O.RULE_REDUCE $ [_ \ sels] => R.Computation.Reduce sign (Syntax.outVec' Syntax.outSelector sels)
     | O.POLY (O.RULE_UNFOLD_ALL opids) $ _ => R.Custom.UnfoldAll sign opids
     | O.POLY (O.RULE_UNFOLD opids) $ [_ \ vec] => R.Custom.Unfold sign opids (Syntax.outVec' Syntax.outSelector vec)
     | O.MONO (O.RULE_PRIM ruleName) $ _ => R.lookupRule ruleName
     | O.MONO O.DEV_LET $ [_ \ jdg, _ \ tm1, ([],[u]) \ tm2] => R.Cut (AJ.out jdg) thenl' ([u], [tactic sign env tm1, tactic sign env tm2])
     | O.MONO (O.DEV_FUN_INTRO pats) $ [(_, us) \ tm] => funIntros sign (pats, us) (tactic sign env tm)
     | O.MONO (O.DEV_RECORD_INTRO lbls) $ args => recordIntro sign lbls (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.MONO (O.DEV_PATH_INTRO _) $ [([], us) \ tm] => pathIntros sign us (tactic sign env tm)
     | O.MONO O.DEV_BOOL_ELIM $ [_ \ var, _ \ tm1, _ \ tm2] => elimRule sign (VarKit.fromTerm var) [] [tactic sign env tm1, tactic sign env tm2]
     | O.MONO O.DEV_S1_ELIM $ [_ \ var, _ \ tm1, (_, [v]) \ tm2] => elimRule sign (VarKit.fromTerm var) [v] [tactic sign env tm1, tactic sign env tm2, autoTac sign, autoTac sign, autoTac sign]
     | O.MONO (O.DEV_APPLY_HYP pattern) $ [_ \ var, _ \ vec, (_, names) \ tm'] =>
       let
         val z = VarKit.fromTerm var
         val tacs = Syn.outVec' (tactic sign env) vec
         val _ = RedPrlLog.print RedPrlLog.INFO (getAnnotation tm, TermPrinter.ppTerm tm)
         val tac = tactic sign env tm'
       in
         applications sign z (pattern, names) tacs tac
       end
     | O.MONO O.DEV_USE_HYP $ [_ \ var, _ \ vec] => 
       let
         val z = VarKit.fromTerm var
         val tacs = Syntax.outVec' (tactic sign env) vec
         val z' = RedPrlSym.named (Sym.toString z ^ "'")
       in
         applications sign z (O.PAT_VAR (), [z']) tacs (hyp z')
       end


       (* TODO: check all these weird list reversals *)
     | O.POLY (O.DEV_APPLY_LEMMA (opid, ar, pat)) $ args =>
       let
         val (([], names) \ tac) :: (_ \ vec) :: revSubtermArgs = List.rev args
         val subtermArgs = List.rev revSubtermArgs
         val O.MONO (O.MK_VEC _) $ appArgs = Tm.out vec

         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
         val tac = tactic sign env tm
       in
         cutLemma sign opid (Option.valOf ar) (List.rev subtermArgs) (pat, names) (List.rev appTacs) tac
       end
     | O.POLY (O.DEV_USE_LEMMA (opid, ar)) $ args =>
       let
         val (_ \ vec) :: revSubtermArgs = List.rev args
         val subtermArgs = List.rev revSubtermArgs
         val O.MONO (O.MK_VEC _) $ appArgs = Tm.out vec

         val z = RedPrlSym.named (Sym.toString opid ^ "'")
         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
       in
         cutLemma sign opid (Option.valOf ar) (List.rev subtermArgs) (O.PAT_VAR (), [z]) (List.rev appTacs) (hyp z)
       end
     | O.POLY (O.CUST (opid, _)) $ args => tactic sign env (unfoldCustomOperator sign (opid, args))
     | O.MONO (O.DEV_MATCH (tau, ns)) $ (_ \ term) :: clauses =>
       let
         fun defrostMetas metas =
           let
             fun go tm = 
               case out tm of
                  O.POLY (O.PAT_META (x, tau, taus)) $ args =>
                   if Unify.Metas.member metas x then 
                    check (x $# ([], List.map (fn _ \ m => m) args), tau)
                   else 
                     tm 
                | _ => tm
           in
             go o deepMapSubterms go
           end

         fun reviveClause ((pvars,_) \ clause) alpha jdg =
           let
             val O.MONO (O.DEV_MATCH_CLAUSE _) $ [_ \ pat, _ \ handler] = out clause
             val metas = Unify.Metas.fromList pvars
             val pat' = defrostMetas metas pat
             val handler' = defrostMetas metas handler
             val rho = Unify.unify metas (term, pat')
               (* handle exn as Unify.Unify (tm1, tm2) => 
                 (RedPrlLog.print RedPrlLog.WARN (getAnnotation pat, Fpp.hsep [Fpp.text "Failed to unify", TermPrinter.ppTerm tm1, Fpp.text "and", TermPrinter.ppTerm tm2]);
                  raise exn) *)
             val handler'' = substMetaenv rho handler'
           in
             tactic sign env handler'' alpha jdg
           end

         fun fail _ _ = raise RedPrlError.error [Fpp.text "No matching clause"]
       in
         List.foldr (fn (clause, tac) => T.orelse_ (reviveClause clause, tac)) fail clauses
       end
     | O.MONO O.DEV_QUERY_GOAL $ [(_,[x]) \ tm] =>
       (fn alpha => fn jdg as _ >> cj =>
         let
           val tm' = substVar (AJ.into cj, x) tm
         in
           tactic sign env tm' alpha jdg
         end)
     | O.MONO (O.DEV_PRINT _) $ [_ \ tm'] =>
       (RedPrlLog.print RedPrlLog.INFO (getAnnotation tm, TermPrinter.ppTerm tm');
        T.idn)
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized tactic", TermPrinter.ppTerm tm]

  and multitactic_ sign env tm =
    case Tm.out tm of 
       O.MONO O.MTAC_ALL $ [_ \ tm] => T.all (tactic sign env tm)
     | O.MONO (O.MTAC_EACH _) $ args => T.each (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.MONO (O.MTAC_FOCUS i) $ [_ \ tm] => T.only (i, tactic sign env tm)
     | O.MONO O.MTAC_PROGRESS $ [_ \ tm] => T.mprogress (multitactic sign env tm)
     | O.MONO O.MTAC_REC $ [(_,[x]) \ tm] => T.mrec (fn mt => multitactic sign (Var.Ctx.insert env x mt) tm)
     | O.MONO (O.MTAC_SEQ _) $ [_ \ tm1, (_, us) \ tm2] => T.seq (multitactic sign env tm1, (us, multitactic sign env tm2))
     | O.MONO O.MTAC_ORELSE $ [_ \ tm1, _ \ tm2] => T.morelse (multitactic sign env tm1, multitactic sign env tm2)
     | O.MONO (O.MTAC_HOLE msg) $ _ => hole (Option.valOf (Tm.getAnnotation tm), msg)
     | O.MONO O.MTAC_REPEAT $ [_ \ tm] => T.mrepeat (multitactic sign env tm)
     | O.MONO O.MTAC_AUTO $ _ => autoMtac sign
     | O.POLY (O.CUST (opid, _)) $ args => multitactic sign env (unfoldCustomOperator sign (opid, args))
     | `x => Var.Ctx.lookup env x
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized multitactic", TermPrinter.ppTerm tm]

end
