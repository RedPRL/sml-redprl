functor LcfModel (Sig : MINI_SIGNATURE) : NOMINAL_LCF_MODEL =
struct
  structure Lcf = Lcf and Spr = UniversalSpread and E = RedPrlError
  structure Syn = LcfSyntax (Sig)
  structure Machine = NewMachine (Sig)

  type 'a nominal = Syn.atom Spr.point -> 'a
  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal
  type env = multitactic Syn.VarCtx.dict

  open RedPrlAbt
  infix $ \

  structure Rules = Refiner (Sig)

  structure O = RedPrlOpData

  fun hyp z alpha jdg =
    Rules.Hyp.Project z alpha jdg
    handle exn =>
      Rules.Synth.FromWfHyp z alpha jdg
      handle _ => raise exn

  fun interpret (sign, env) rule =
    case out rule of
        O.MONO O.RULE_ID $ _ => (fn _ => Lcf.idn)
      | O.MONO O.RULE_AUTO_STEP $ _ => Rules.AutoStep sign
      | O.POLY (O.RULE_HYP (z, _)) $ _ => hyp z
      | O.POLY (O.RULE_ELIM (z, _)) $ _ => Rules.Elim sign z
      | O.MONO O.RULE_EXACT $ [_ \ tm] => Rules.Exact tm
      | O.MONO O.RULE_HEAD_EXP $ _ => Rules.Computation.EqHeadExpansion sign
      | O.MONO O.RULE_SYMMETRY $ _ => Rules.Equality.Symmetry
      | O.MONO O.RULE_CUT $ [_ \ catjdg] => Rules.Cut (RedPrlCategoricalJudgment.fromAbt catjdg)
      | O.POLY (O.RULE_LEMMA (opid, ps)) $ _ => Rules.Lemma sign opid (List.map #1 ps)
      | O.POLY (O.RULE_CUT_LEMMA (opid, ps)) $ _ => Rules.CutLemma sign opid (List.map #1 ps)
      | O.POLY (O.RULE_UNFOLD opid) $ _ => Rules.Computation.Unfold sign opid
      | _ => raise E.error [Fpp.text "Invalid rule", TermPrinter.ppTerm rule]

  fun rule (sign, env) rule alpha goal =
    Debug.wrap (fn _ => interpret (sign, env) (Machine.eval sign Machine.NOMINAL rule) alpha goal)
    handle exn => raise RedPrlError.annotate (getAnnotation rule) exn

  fun printHole (pos : Pos.t, name : string option) (state : Lcf.jdg Lcf.state) =
    let
      val header = Fpp.seq [Fpp.text (Option.getOpt (name, "hole")), Fpp.char #"."]
      val message = Fpp.vsep [header, Lcf.prettyState state]
    in
      RedPrlLog.print RedPrlLog.INFO (SOME pos, message)
    end
end
