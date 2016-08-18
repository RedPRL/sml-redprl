structure NominalLcfSyntax : NOMINAL_LCF_SYNTAX =
struct
  open RedPrlAbt
  structure Syn = RedPrlAbtSyntax

  structure SymCtx = Symbol.Ctx and VarCtx = Variable.Ctx
  structure O = RedPrlOperator and RO = RedPrlOperators and N = NominalLcfOperators and S = SortData

  infix $ $$ \ $#

  type atom = symbol
  type rule = abt
  type tactic = abt
  type multitactic = abt
  type sign = AbtSignature.sign

  exception hole
  fun ?e = raise e

  fun inheritAnn m n =
    case Syn.getAnnotation m of
       SOME ann => annotate ann n
     | NONE => n

  fun evalOpen sign t =
    inheritAnn t (RedPrlDynamics.eval sign t)
      handle _ => t

  local
    fun go syms m =
      (case Syn.out m of
         Syn.HYP_REF a =>
           if SymCtx.member syms a then
             m
           else
             inheritAnn m (check (`a, O.S.EXP S.EXP))
       | _ => raise Match)
      handle _ => goStruct syms m

    and goStruct syms m =
      let
        val (m', tau) = infer m
      in
        inheritAnn m
          (case out m of
             theta $ es =>
               theta $$ List.map (goAbs syms) es
           | x $# (us, ms) =>
               check (x $# (us, List.map (go syms) ms), tau)
           | _ => m)
      end

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

  structure Multitactic =
  struct
    exception InvalidMultitactic

    datatype view =
        ALL of tactic
      | EACH of tactic list
      | FOCUS of int * tactic

    fun out sign mtac =
      case Syn.out (expandHypVars (evalOpen sign mtac)) of
           Syn.MTAC_ALL t => ALL t
         | Syn.MTAC_EACH ts => EACH ts
         | Syn.MTAC_FOCUS (u, t) => FOCUS (u, t)
         | _ => raise InvalidMultitactic
  end

  structure Tactic =
  struct
    exception InvalidStatement

    type 'a binding = symbol list * 'a

    datatype view =
        SEQ of multitactic binding list
      | ORELSE of tactic * tactic
      | REC of variable * tactic
      | PROGRESS of tactic
      | RULE of rule
      | VAR of variable

    fun collect t =
      (case Syn.out t of
           Syn.TAC_SEQ (mt, us, t') => (List.map #1 us, mt) :: collect t'
         | _ => raise Match)
      handle _ => [([], Syn.into (Syn.MTAC_ALL t))]

    fun out sign t =
      let
        val t' = inheritAnn t (expandHypVars (evalOpen sign t))
      in
        case Syn.outOpen t' of
           Syn.VAR x => VAR x
         | Syn.APP view =>
             (case view of
                 Syn.TAC_SEQ _ => SEQ (collect t')
               | Syn.TAC_ORELSE (t1, t2) => ORELSE (t1, t2)
               | Syn.TAC_REC (x, t) => REC (x, t)
               | Syn.TAC_PROGRESS t => PROGRESS t
               | _ => RULE t')
         | _ => RULE t'
      end
  end
end
