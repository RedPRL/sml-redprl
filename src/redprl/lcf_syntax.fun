functor LcfSyntax (Sig : MINI_SIGNATURE) : NOMINAL_LCF_SYNTAX =
struct
  structure Machine = RedPrlMachine (Sig)
  structure Tm = RedPrlAbt open RedPrlAbt
  structure O = RedPrlOpData
  infix $ $$ \ $#

  structure SymCtx = Sym.Ctx and VarCtx = Var.Ctx

  type atom = symbol
  type rule = abt
  type tactic = abt
  type multitactic = abt
  type sign = Sig.sign
  type ann = Pos.t * string option

  fun inheritAnnotation t1 t2 =
    case getAnnotation t2 of
       NONE => setAnnotation (getAnnotation t1) t2
     | _ => t2

  fun evalOpen sign t =
    inheritAnnotation t (Machine.eval sign t)
      handle _ => t

  local
    fun go syms m =
      case Tm.out m of
         O.POLY (O.HYP_REF a) $ _ =>
           if SymCtx.member syms a then
             m
           else
             inheritAnnotation m (check (`a, O.EXP))
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
        val syms' = List.foldl (fn (u, acc) => SymCtx.insert acc u ()) syms us
      in
        (us,xs) \ go syms' m
      end
  in
    (* Replace hypothesis-references @u with variables `u; this will *only* expand
     * unbound hyp-refs. *)
   val expandHypVars =
      go SymCtx.empty
  end

  exception InvalidStatement
  exception InvalidMultitactic (* unused but demanded by the signature *)

  open NominalLcfView

  fun prepareTerm sign t =
    inheritAnnotation t
      (expandHypVars (evalOpen sign t))

  fun tactic sign tac =
    let
      val tac' = prepareTerm sign tac
    in
      case Tm.out tac' of
         O.MONO O.TAC_MTAC $ [_ \ mt] => MTAC (inheritAnnotation tac' mt)
       | _ => RULE tac'
    end

  fun multitactic sign mtac =
    case Tm.out (prepareTerm sign mtac) of
         O.MONO O.MTAC_ALL $ [_ \ t] => ALL (SEQUENTIAL, inheritAnnotation mtac t)
       | O.MONO (O.MTAC_EACH _) $ ts => EACH (SEQUENTIAL, List.map (fn _ \ t => inheritAnnotation mtac t) ts)
       | O.MONO (O.MTAC_FOCUS i) $ [_ \ t] => FOCUS (i, inheritAnnotation mtac t)
       | O.MONO O.MTAC_PROGRESS $ [_ \ mt] => PROGRESS (inheritAnnotation mtac mt)
       | O.MONO O.MTAC_REC $ [(_,[x]) \ mtx] => REC (x, inheritAnnotation mtac mtx)
       | O.MONO (O.MTAC_SEQ _) $ [_ \ mt1, (us,_) \ mt2] => SEQ (us, inheritAnnotation mtac mt1, inheritAnnotation mtac mt2)
       | O.MONO O.MTAC_ORELSE $ [_ \ mt1, _ \ mt2] => ORELSE (inheritAnnotation mtac mt1, inheritAnnotation mtac mt2)
       | O.MONO (O.MTAC_HOLE msg) $ _ => HOLE (Option.valOf (getAnnotation mtac), msg)
       | ` x => VAR x
       | _ => raise InvalidMultitactic
end
