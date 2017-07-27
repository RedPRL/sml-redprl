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
    (* Replace hypothesis-references @u with variables `u; this will *only* expand
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
      elimRule sign z xs [tac] alpha jdg
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

  fun decomposeStitched sign z (pattern : Sym.t O.dev_pattern) tac = 
    case pattern of 
        O.PAT_VAR u => R.Hyp.Rename z thenl' ([u], [tac])
      | O.PAT_TUPLE labeledPatterns =>
        let
          val (lbls, pats) = ListPair.unzip labeledPatterns
          val names = List.map (fn lbl => Sym.named ("tmp/" ^ lbl)) lbls

          val rec go = 
            fn [] => tac
            | (name, pat) :: rest => decomposeStitched sign name pat (R.Hyp.Delete name thenl [go rest])

          val continue = go (ListPair.zip (names, pats))
        in
          recordElim sign z (lbls, names) continue
        end

  fun decompose sign z =
    decomposeStitched sign z
      o #1
      o stitchPattern

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
            | _ => decomposeStitched sign name pat' (R.Hyp.Delete name thenl [intros])
       in
         RT.DFun.True thenl' ([name], [continue, autoTac sign])
       end
    (* case us of 
       [] => tac
     | u::us => RT.DFun.True thenl' ([u], [dfunIntros sign us tac, autoTac sign]) *)

  fun pathIntros sign us tac =
    case us of 
       [] => tac
     | u::us => RT.Path.True thenl' ([u], [pathIntros sign us tac, autoTac sign, autoTac sign])


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
     | O.POLY (O.RULE_HYP (z, _)) $ _ => hyp z
     | O.MONO (O.RULE_EXACT _) $ [_ \ tm] => R.Exact (expandHypVars tm)
     | O.MONO O.RULE_HEAD_EXP $ _ => R.Computation.EqHeadExpansion sign
     | O.MONO O.RULE_SYMMETRY $ _ => R.Equality.Symmetry
     | O.MONO O.RULE_CUT $ [_ \ catjdg] => R.Cut (CJ.fromAbt (expandHypVars catjdg))
     | O.POLY (O.RULE_LEMMA (opid, ps)) $ _ => R.Lemma sign opid (List.map #1 ps)
     | O.POLY (O.RULE_CUT_LEMMA (opid, ps)) $ _ => R.CutLemma sign opid (List.map #1 ps)
     | O.POLY (O.RULE_UNFOLD opid) $ _ => R.Computation.Unfold sign opid
     | O.MONO (O.RULE_PRIM ruleName) $ _ => R.lookupRule ruleName
     | O.MONO (O.DEV_LET tau) $ [_ \ jdg, _ \ tm1, ([u],_) \ tm2] => R.Cut (CJ.fromAbt (expandHypVars jdg)) thenl' ([u], [tactic sign env tm1, tactic sign env tm2])
     | O.MONO (O.DEV_DFUN_INTRO pats) $ [(us, _) \ tm] => dfunIntros sign (pats, us) (tactic sign env tm)
     | O.MONO (O.DEV_RECORD_INTRO lbls) $ args => recordIntro sign lbls (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.MONO (O.DEV_PATH_INTRO _) $ [(us, _) \ tm] => pathIntros sign us (tactic sign env tm)
     | O.POLY (O.DEV_BOOL_ELIM z) $ [_ \ tm1, _ \ tm2] => elimRule sign z [] [tactic sign env tm1, tactic sign env tm2]
     | O.POLY (O.DEV_S1_ELIM z) $ [_ \ tm1, ([v], _) \ tm2] => elimRule sign z [v] [tactic sign env tm1, tactic sign env tm2, autoTac sign, autoTac sign]
     | O.POLY (O.DEV_DFUN_ELIM z) $ [_ \ tm1, ([x,p],_) \ tm2] => elimRule sign z [x,p] [tactic sign env tm1, tactic sign env tm2]
     | O.POLY (O.DEV_PATH_ELIM z) $ [_ \ tm1, ([x,p], _) \ tm2] => elimRule sign z [x,p] [tactic sign env tm1, autoTac sign, autoTac sign, tactic sign env tm2]
     | O.POLY (O.DEV_DECOMPOSE (z, pattern)) $ [(us, _) \ tm] => decompose sign z (pattern, us) (tactic sign env tm)
     | O.POLY (O.CUST (opid, ps, _)) $ args => tactic sign env (unfoldCustomOperator sign (opid, ps, args))
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