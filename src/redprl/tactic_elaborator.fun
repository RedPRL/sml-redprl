functor TacticElaborator (Sig : MINI_SIGNATURE) :
sig
  type script = RedPrlAbt.abt

  type 'a nominal = (int -> Sym.t) -> 'a
  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal

  type env = multitactic Var.Ctx.dict

  val tactic : env -> script -> tactic
  val multitactic : env -> script -> multitactic
end = 
struct
  structure Tm = RedPrlAbt
  type script = Tm.abt

  structure LcfStructure =
  struct
    structure Lcf = Lcf and Spr = UniversalSpread
    type 'a nominal = (int -> Sym.t) -> 'a
    type tactic = Lcf.jdg Lcf.tactic nominal
    type multitactic = Lcf.jdg Lcf.multitactic nominal
  end

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

  fun tactic env tm = ?todo

  and multitactic env tm =
    case out tm of 
       O.MONO O.MTAC_ALL $ [_ \ tm] => T.all (tactic env tm)
     | O.MONO (O.MTAC_EACH _) $ args => T.each (List.map (fn _ \ tm => tactic env tm) args)
     | O.MONO (O.MTAC_FOCUS i) $ [_ \ tm] => T.only (i, tactic env tm)
     | O.MONO O.MTAC_PROGRESS $ [_ \ tm] => T.mprogress (multitactic env tm)
     | O.MONO O.MTAC_REC $ [(_,[x]) \ tm] => T.mrec (fn mt => multitactic (Var.Ctx.insert env x mt) tm)
     | O.MONO (O.MTAC_SEQ _) $ [_ \ tm1, (us, _) \ tm2] => T.seq (multitactic env tm1, us, multitactic env tm2)
     | O.MONO O.MTAC_ORELSE $ [_ \ tm1, _ \ tm2] => T.morelse (multitactic env tm1, multitactic env tm2)
     | O.MONO (O.MTAC_HOLE msg) $ _ => hole (Option.valOf (Tm.getAnnotation tm), msg)
     | `x => Var.Ctx.lookup env x
     | _ => raise RedPrlError.error [Fpp.text "Unrecognized multitactic", TermPrinter.ppTerm tm]

end