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

  fun autoMtac sign = mrepeat (all (try (R.AutoStep sign)))
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

  fun tactic sign env tm alpha jdg = 
    tactic_ sign env (expandHypVars tm) alpha jdg 
    handle exn => 
      raise RedPrlError.annotate (Tm.getAnnotation tm) exn

  and multitactic sign env tm alpha jdg = 
    multitactic_ sign env (expandHypVars tm) alpha jdg
    handle exn => 
      raise RedPrlError.annotate (Tm.getAnnotation tm) exn

  and tactic_ sign env tm = 
    case Tm.out tm of 
       O.MONO O.TAC_MTAC $ [_ \ tm] => multitacToTac (multitactic sign env tm)
     | O.MONO O.RULE_ID $ _ => idn
     | O.MONO O.RULE_AUTO_STEP $ _ => R.AutoStep sign
     | O.POLY (O.RULE_ELIM (z, _)) $ _ => R.Elim sign z
     | O.POLY (O.RULE_HYP (z, _)) $ _ => hyp z
     | O.MONO (O.RULE_EXACT _) $ [_ \ tm] => R.Exact tm
     | O.MONO O.RULE_HEAD_EXP $ _ => R.Computation.EqHeadExpansion sign
     | O.MONO O.RULE_SYMMETRY $ _ => R.Equality.Symmetry
     | O.MONO O.RULE_CUT $ [_ \ catjdg] => R.Cut (CJ.fromAbt catjdg)
     | O.POLY (O.RULE_LEMMA (opid, ps)) $ _ => R.Lemma sign opid (List.map #1 ps)
     | O.POLY (O.RULE_CUT_LEMMA (opid, ps)) $ _ => R.CutLemma sign opid (List.map #1 ps)
     | O.POLY (O.RULE_UNFOLD opid) $ _ => R.Computation.Unfold sign opid
     | O.MONO (O.RULE_PRIM ruleName) $ _ => R.lookupRule ruleName
     | O.MONO (O.DEV_LET tau) $ [_ \ jdg, _ \ tm1, ([u],_) \ tm2] => R.Cut (CJ.fromAbt jdg) thenl' ([u], [tactic sign env tm1, tactic sign env tm2])
     | O.MONO O.DEV_DFUN_INTRO $ [([u], _) \ tm] => RT.DFun.True thenl' ([u], [tactic sign env tm, autoTac sign])
     | O.MONO O.DEV_DPROD_INTRO $ [_ \ tm1, _ \ tm2] => RT.DProd.True thenl [tactic sign env tm1, tactic sign env tm2, autoTac sign]
     | O.MONO O.DEV_PATH_INTRO $ [([u], _) \ tm] => RT.Path.True thenl' ([u], [tactic sign env tm, autoTac sign, autoTac sign])
     | O.POLY (O.DEV_BOOL_ELIM z) $ [_ \ tm1, _ \ tm2] => elimRule sign z [] [tactic sign env tm1, tactic sign env tm2]
     | O.POLY (O.DEV_S1_ELIM z) $ [_ \ tm1, ([v], _) \ tm2] => elimRule sign z [v] [tactic sign env tm1, tactic sign env tm2, autoTac sign, autoTac sign]
     | O.POLY (O.DEV_DFUN_ELIM z) $ [_ \ tm1, ([x,p],_) \ tm2] => elimRule sign z [x,p] [tactic sign env tm1, tactic sign env tm2]
     | O.POLY (O.DEV_DPROD_ELIM z) $ [([x,y], _) \ tm] => elimRule sign z [x,y] [tactic sign env tm]
     | O.POLY (O.DEV_PATH_ELIM z) $ [_ \ tm1, ([x,p], _) \ tm2] => elimRule sign z [x,p] [tactic sign env tm1, autoTac sign, autoTac sign, tactic sign env tm2]
     | O.POLY (O.DEV_RECORD_ELIM (z, lbls)) $ [(us, _) \ tm] => recordElim sign z (lbls, us) (tactic sign env tm)
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