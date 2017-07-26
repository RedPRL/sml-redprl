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

  structure LcfStructure =
  struct
    structure Lcf = Lcf and Spr = UniversalSpread
    type 'a nominal = (int -> Sym.t) -> 'a
    type tactic = Lcf.jdg Lcf.tactic nominal
    type multitactic = Lcf.jdg Lcf.multitactic nominal
  end

  structure R = Refiner (Sig)
  structure T = NominalLcfTactical (LcfStructure)
  open LcfStructure

  type env = multitactic Var.Ctx.dict

  fun ?e = raise e
  exception todo

  open Tm infix $ \
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
      R.Synth.FromWfHyp z alpha jdg
      handle _ => raise exn


  structure CJ = RedPrlCategoricalJudgment

  fun tactic sign env tm = 
    case Tm.out tm of 
       O.MONO O.TAC_MTAC $ [_ \ tm] => T.multitacToTac (multitactic sign env tm)
     | O.MONO O.RULE_ID $ _ => T.idn
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
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized tactic", TermPrinter.ppTerm tm]
     (* TODO: elaborate "defined tactics", which are currently defined in the machine *)

  and multitactic sign env tm =
    case Tm.out tm of 
       O.MONO O.MTAC_ALL $ [_ \ tm] => T.all (tactic sign env tm)
     | O.MONO (O.MTAC_EACH _) $ args => T.each (List.map (fn _ \ tm => tactic sign env tm) args)
     | O.MONO (O.MTAC_FOCUS i) $ [_ \ tm] => T.only (i, tactic sign env tm)
     | O.MONO O.MTAC_PROGRESS $ [_ \ tm] => T.mprogress (multitactic sign env tm)
     | O.MONO O.MTAC_REC $ [(_,[x]) \ tm] => T.mrec (fn mt => multitactic sign (Var.Ctx.insert env x mt) tm)
     | O.MONO (O.MTAC_SEQ _) $ [_ \ tm1, (us, _) \ tm2] => T.seq (multitactic sign env tm1, us, multitactic sign env tm2)
     | O.MONO O.MTAC_ORELSE $ [_ \ tm1, _ \ tm2] => T.morelse (multitactic sign env tm1, multitactic sign env tm2)
     | O.MONO (O.MTAC_HOLE msg) $ _ => hole (Option.valOf (Tm.getAnnotation tm), msg)
     | `x => Var.Ctx.lookup env x
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized multitactic", TermPrinter.ppTerm tm]

end