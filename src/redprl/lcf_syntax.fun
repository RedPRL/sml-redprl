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

  fun evalOpen sign t =
    setAnnotation (getAnnotation t) (Machine.eval sign t)
      handle _ => t

  local
    fun go syms m =
      case Tm.out m of
         O.POLY (O.HYP_REF a) $ _ =>
           if SymCtx.member syms a then
             m
           else
             setAnnotation (getAnnotation m) (check (`a, O.EXP))
       | _ => goStruct syms m

    and goStruct syms m =
      setAnnotation (getAnnotation m)
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
  exception InvalidMultitactic

  open NominalLcfView

  fun prepareTerm sign t =
    setAnnotation
      (getAnnotation t)
      (expandHypVars (evalOpen sign t))

  local
    fun collect t =
      case Tm.out t of
         O.MONO (O.TAC_SEQ n) $ [_ \ mt, (us,_) \ t'] => (us, mt) :: collect t'
       | _ => [([], O.MONO O.MTAC_ALL $$ [([],[]) \ t])]

  in
    fun tactic sign tac =
      let
        val tac' = prepareTerm sign tac
      in
        case Tm.out tac' of
           `x => VAR x
         | O.MONO (O.TAC_SEQ _) $ _ => SEQ (collect tac')
         | O.MONO O.TAC_ORELSE $ [_ \ t1, _ \ t2] => ORELSE (t1, t2)
         | O.MONO O.TAC_REC $ [(_,[x]) \ tx] => REC (x, tx)
         | _ => RULE tac'
         (* TODO: ORELSE, REC, PROGRESS, etc. *)
      end
  end

  fun multitactic sign mtac =
    case Tm.out (prepareTerm sign mtac) of
         O.MONO O.MTAC_ALL $ [_ \ t] => ALL t
       | O.MONO (O.MTAC_EACH _) $ ts => EACH (List.map (fn _ \ t => t) ts)
       | O.MONO (O.MTAC_FOCUS i) $ [_ \ t] => FOCUS (i, t)
       | _ => raise InvalidMultitactic
end
