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

  local
    fun inheritAnnotation t1 t2 =
      case getAnnotation t2 of
         NONE => setAnnotation (getAnnotation t1) t2
       | _ => t2

    fun go syms m =
      case Tm.out m of
         O.POLY (O.HYP_REF a) $ _ =>
           if Sym.Ctx.member syms a then
             m
           else
             inheritAnnotation m (check (`a, O.EXP)) 
              (* TODO: This can't be right *)
       | _ => goStruct syms m

    and goStruct syms m =
      inheritAnnotation m
        (case out m of
           theta $ es =>
             theta $$ List.map (goAbs syms) es
         | x $# (ps, ms) =>
             check (x $# (ps, List.map (go syms) ms), sort m)
         | _ => m)

    and goAbs syms ((us,xs) \ m) =
      let
        val syms' = List.foldl (fn (u, acc) => Sym.Ctx.insert acc u ()) syms us
      in
        (us,xs) \ go syms' m
      end
  in
    (* Replace hypothesis-references with variables; this will *only* expand
     * unbound hyp-refs. *)
    val expandHypVars = go Sym.Ctx.empty
  end

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
      R.Synth.FromWfHyp z alpha jdg
      handle _ => raise exn

  open RedPrlSequent infix >>
  structure CJ = RedPrlCategoricalJudgment and Syn = Syntax

  val autoMtac = mrepeat o all o try o R.AutoStep
  val autoTac = multitacToTac o autoMtac

  fun unfoldCustomOperator sign (opid, ps, args) = 
    let
      val entry as {state, ...} = Sig.lookup sign opid
      val state = state (fn _ => RedPrlSym.new ())
      val (mrho, srho) = Sig.applyCustomOperator entry (List.map (fn (r, _) => r) ps) args
    in
      substSymenv srho (substMetaenv mrho (Sig.extract state))
    end

  fun elimRule sign z xs tacs = 
    R.Elim sign z thenl' (xs, tacs)

  fun recordElim sign z (lbls, names) tac alpha jdg =
    let
      val (_, H) >> _ = jdg
      val CJ.TRUE record = RT.lookupHyp H z
      val Syn.RECORD fields = Syn.out record
      val nameMap = ListPair.foldl (fn (lbl, name, r) => Syn.LabelDict.insert r lbl name) Syn.LabelDict.empty (lbls, names)
      fun nameForLabel lbl = 
        Syn.LabelDict.lookup nameMap lbl
        handle Syn.LabelDict.Absent => Sym.named ("@" ^ lbl)
      val xs = List.map (fn ((lbl, _), _) => nameForLabel lbl) fields
    in
      (RT.Record.Elim z thenl' (xs, [tac])) alpha jdg
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
          recordElim sign z (lbls, names) continue
        end

  fun decompose sign z =
    decomposeStitched sign z
      o #1
      o stitchPattern

  fun apply sign z names (appTac, contTac) alpha jdg = 
    let
      val (_, H) >> _ = jdg
      val CJ.TRUE ty = RT.lookupHyp H z
    in
      case Syn.out ty of 
         Syn.DFUN _ => (RT.DFun.Elim z thenl' (names, [appTac, contTac])) alpha jdg
       | Syn.PATH_TY _ => (RT.Path.Elim z thenl' (names, [appTac, autoTac sign, autoTac sign, contTac])) alpha jdg
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

  fun recordIntro sign lbls tacs alpha jdg = 
    let
      val (_, _) >> CJ.TRUE record = jdg
      val Syn.RECORD fields = Syn.out record

      val labeledTactics = ListPair.zipEq (lbls, tacs)

      fun tacticForLabel lbl = 
        case ListUtil.findIndex (fn (lbl', _) => lbl = lbl') labeledTactics of
           SOME (_, (_, tac)) => tac
         | NONE => idn

      val fieldTactics = List.map (fn ((lbl, _), _) => tacticForLabel lbl) fields
      val famTactics = List.tabulate (List.length fields - 1, fn _ => autoTac sign)
    in
      (RT.Record.True thenl fieldTactics @ famTactics) alpha jdg
    end


  fun nameForPattern pat = 
    case pat of 
       O.PAT_VAR x => x
     | O.PAT_TUPLE lpats => Sym.named (ListSpine.pretty (Sym.toString o nameForPattern o #2) "-" lpats)

  fun dfunIntros sign (pats, names) tac =
    case pats of 
       [] => tac
     | pat::pats => 
       let
         val (pat', names') = stitchPattern (pat, names)
         val name = nameForPattern pat'
         val intros = dfunIntros sign (pats, names') tac
         val continue =
           case pat' of
              O.PAT_VAR _ => intros
            | _ => decomposeStitched sign name pat' (deleteHyp name thenl [intros])
       in
         RT.DFun.True thenl' ([name], [continue, autoTac sign])
       end

  fun pathIntros sign us tac =
    case us of 
       [] => tac
     | u::us => RT.Path.True thenl' ([u], [pathIntros sign us tac, autoTac sign, autoTac sign])


  fun exactAuto sign m = 
    R.Exact (expandHypVars m) thenl [autoTac sign]

  fun cutLemma sign opid ar ps (args : abt bview list) (pattern, names) appTacs tac =
    let
      val (vls, _) = ar
      fun processArg ((us, xs) \ m, ((sigmas, taus), _), {subtermNames, subtermTacs}) =
        let
          val syms = ListPair.zipEq (us, sigmas)
          val vars = ListPair.mapEq (fn (x, tau) => (x, O.HYP tau)) (xs, taus)
          val rho = ListPair.foldl (fn (x, tau, rho) => Var.Ctx.insert rho x (O.POLY (O.HYP_REF x) $$ [])) Var.Ctx.empty (xs, taus)
          val m' = substVarenv rho m
        in
          {subtermNames = us @ xs @ subtermNames,
           subtermTacs = exactAuto sign m' :: subtermTacs}
        end

      val {subtermNames, subtermTacs} = ListPair.foldr processArg {subtermNames = [], subtermTacs = []} (args, vls)

      val z = RedPrlSym.new ()
      val continue = applications sign z (pattern, names) appTacs tac
    in
      R.CutLemma sign opid ps thenl' (z :: subtermNames, subtermTacs @ [continue])
    end

  fun tactic sign env tm alpha jdg = 
    tactic_ sign env tm alpha jdg 
    handle exn => 
      raise RedPrlError.annotate (Tm.getAnnotation tm) exn

  and multitactic sign env tm alpha jdg = 
    multitactic_ sign env tm alpha jdg
    handle exn => 
      raise RedPrlError.annotate (Tm.getAnnotation tm) exn

  and tactic_ sign env tm = 
    case Tm.out tm of 
       O.MONO O.TAC_MTAC $ [_ \ tm] => multitacToTac (multitactic sign env tm)
     | O.MONO O.RULE_ID $ _ => idn
     | O.MONO O.RULE_AUTO_STEP $ _ => R.AutoStep sign
     | O.POLY (O.RULE_ELIM (z, _)) $ _ => R.Elim sign z
     | O.MONO (O.RULE_EXACT _) $ [_ \ tm] => R.Exact (expandHypVars tm)
     | O.MONO O.RULE_HEAD_EXP $ _ => R.Computation.EqHeadExpansion sign
     | O.MONO O.RULE_SYMMETRY $ _ => R.Equality.Symmetry
     | O.MONO O.RULE_CUT $ [_ \ catjdg] => R.Cut (CJ.fromAbt (expandHypVars catjdg))
     | O.POLY (O.RULE_UNFOLD opid) $ _ => R.Computation.Unfold sign opid
     | O.MONO (O.RULE_PRIM ruleName) $ _ => R.lookupRule ruleName
     | O.MONO (O.DEV_LET tau) $ [_ \ jdg, _ \ tm1, ([u],_) \ tm2] => R.Cut (CJ.fromAbt (expandHypVars jdg)) thenl' ([u], [tactic sign env tm1, tactic sign env tm2])
     | O.MONO (O.DEV_DFUN_INTRO pats) $ [(us, _) \ tm] => dfunIntros sign (pats, us) (tactic sign env tm)
     | O.MONO (O.DEV_RECORD_INTRO lbls) $ args => recordIntro sign lbls (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.MONO (O.DEV_PATH_INTRO _) $ [(us, _) \ tm] => pathIntros sign us (tactic sign env tm)
     | O.POLY (O.DEV_BOOL_ELIM z) $ [_ \ tm1, _ \ tm2] => elimRule sign z [] [tactic sign env tm1, tactic sign env tm2]
     | O.POLY (O.DEV_S1_ELIM z) $ [_ \ tm1, ([v], _) \ tm2] => elimRule sign z [v] [tactic sign env tm1, tactic sign env tm2, autoTac sign, autoTac sign]
     | O.POLY (O.DEV_APPLY_HYP (z, pattern, _)) $ args =>
       let
         val ((names, _) \ tm) :: args' = List.rev args
         val tacs = List.map (fn _ \ tm => tactic sign env tm) (List.rev args')
         val tac = tactic sign env tm
       in
         applications sign z (pattern, names) tacs tac
       end
     | O.POLY (O.DEV_USE_HYP (z, n)) $ args => 
       let
         val z' = RedPrlSym.named (Sym.toString z ^ "'")
         val tacs = List.map (fn _ \ tm => tactic sign env tm) args
       in
         applications sign z (O.PAT_VAR (), [z']) tacs (hyp z')
       end
     | O.POLY (O.DEV_APPLY_LEMMA (opid, ps, ar, pat, n)) $ args =>
       let
         val ((names, []) \ tm) :: args' = List.rev args
         val (appArgs, subtermArgs) = ListUtil.splitAt (args', n)
         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
         val tac = tactic sign env tm
       in
         cutLemma sign opid (Option.valOf ar) ps (List.rev subtermArgs) (pat, names) (List.rev appTacs) tac
       end
     | O.POLY (O.DEV_USE_LEMMA (opid, ps, ar, n)) $ args =>
       let
         val z = RedPrlSym.named (Sym.toString opid ^ "'")
         val (appArgs, subtermArgs) = ListUtil.splitAt (List.rev args, n)
         val appTacs = List.map (fn _ \ tm => tactic sign env tm) appArgs
       in
         cutLemma sign opid (Option.valOf ar) ps (List.rev subtermArgs) (O.PAT_VAR (), [z]) (List.rev appTacs) (hyp z)
       end
     | O.POLY (O.CUST (opid, ps, _)) $ args => tactic sign env (unfoldCustomOperator sign (opid, ps, args))
     | O.MONO (O.DEV_MATCH (tau, ns)) $ (_ \ term) :: clauses =>
       let
         fun defrostMetas metas =
           let
             fun go tm = 
               case out tm of
                  O.POLY (O.PAT_META (x, tau, rs, taus)) $ args =>
                   if Unify.Metas.member metas x then 
                    check (x $# (rs, List.map (fn _ \ m => m) args), tau)
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
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized tactic", TermPrinter.ppTerm tm]

  and multitactic_ sign env tm =
    case Tm.out tm of 
       O.MONO O.MTAC_ALL $ [_ \ tm] => T.all (tactic sign env tm)
     | O.MONO (O.MTAC_EACH _) $ args => T.each (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.MONO (O.MTAC_FOCUS i) $ [_ \ tm] => T.only (i, tactic sign env tm)
     | O.MONO O.MTAC_PROGRESS $ [_ \ tm] => T.mprogress (multitactic sign env tm)
     | O.MONO O.MTAC_REC $ [(_,[x]) \ tm] => T.mrec (fn mt => multitactic sign (Var.Ctx.insert env x mt) tm)
     | O.MONO (O.MTAC_SEQ _) $ [_ \ tm1, (us, _) \ tm2] => T.seq (multitactic sign env tm1, (us, multitactic sign env tm2))
     | O.MONO O.MTAC_ORELSE $ [_ \ tm1, _ \ tm2] => T.morelse (multitactic sign env tm1, multitactic sign env tm2)
     | O.MONO (O.MTAC_HOLE msg) $ _ => hole (Option.valOf (Tm.getAnnotation tm), msg)
     | O.MONO O.MTAC_REPEAT $ [_ \ tm] => T.mrepeat (multitactic sign env tm)
     | O.MONO O.MTAC_AUTO $ _ => autoMtac sign
     | O.POLY (O.CUST (opid, ps, _)) $ args => multitactic sign env (unfoldCustomOperator sign (opid, ps, args))
     | `x => Var.Ctx.lookup env x
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized multitactic", TermPrinter.ppTerm tm]

end