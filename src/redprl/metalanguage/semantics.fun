functor MlSemantics
  (Syn : ML_SYNTAX
    where type jdg = AtomicJudgment.jdg
      and type term = RedPrlAbt.abt
      and type metavariable = RedPrlAbt.metavariable) : ML_SEMANTICS = 
struct
  type term = Syn.term
  type jdg = Syn.jdg
  type metavariable = Syn.metavariable
  type metas = Syn.metas
  type syn_cmd = Syn.cmd

  structure Dict = SplayDict (structure Key = MlId)

  datatype value =
     THUNK of env * syn_cmd
   | THM of jdg * term
   | TERM of term
   | ABS of value * value
   | METAS of metas
   | NIL

  withtype env = value Dict.dict * metavariable Metavar.Ctx.dict

  datatype cmd =
     RET of value
   | FN of env * MlId.t * syn_cmd

  val initEnv = (Dict.empty, Metavar.Ctx.empty)

  fun @@ (f, x) = f x
  infixr @@  

  fun lookup (env : env) (nm : MlId.t) : value =
    case Dict.find (#1 env) nm of
        SOME v => v
      | NONE =>
        RedPrlError.raiseError @@ 
          RedPrlError.GENERIC
            [Fpp.text "Could not find value of",
             Fpp.text (MlId.toString nm),
             Fpp.text "in environment"]

  fun extend (env : env) (nm : MlId.t) (v : value) : env =
    (Dict.insert (#1 env) nm v, #2 env)

  fun rename (env : env) (Xs : metavariable list) (Ys : metavariable list) =
    (#1 env,
     ListPair.foldrEq
       (fn (X, Y, rho) => Metavar.Ctx.insert rho X Y)
       (#2 env)
       (Xs, Ys))

  fun lookupMeta (env : env) (X : metavariable) = 
    case Metavar.Ctx.find (#2 env) X of 
       SOME Y => Y
     | NONE => 
        RedPrlError.raiseError @@ 
          RedPrlError.GENERIC
            [Fpp.text "Could not find value of metavariable",
             TermPrinter.ppMeta X,
             Fpp.text "in environment"]
     

  fun term (env : env) m = 
    Tm.renameMetavars (#2 env) m

  structure AJ = AtomicJudgment

  (* TODO *)
  val rec ppValue : value -> Fpp.doc =
    fn THUNK _ => Fpp.text "<thunk>"
      | THM (jdg, abt) =>
        Fpp.seq
          [Fpp.text "Thm:",
          Fpp.nest 2 @@ Fpp.seq [Fpp.newline, AJ.pretty jdg],
          Fpp.newline,
          Fpp.newline,
          Fpp.text "Extract:",
          Fpp.nest 2 @@ Fpp.seq [Fpp.newline, TermPrinter.ppTerm abt]]

      | TERM abt =>
        TermPrinter.ppTerm abt

      | METAS psi =>
        Fpp.collection
          (Fpp.char #"[")
          (Fpp.char #"]")
          Fpp.Atomic.comma
          (List.map (fn (X, vl) => Fpp.hsep [TermPrinter.ppMeta X, Fpp.Atomic.colon, TermPrinter.ppValence vl]) psi)

      | ABS (vpsi, v) =>
        Fpp.seq
          [Fpp.hsep
          [ppValue vpsi,
            Fpp.text "=>"],
          Fpp.nest 2 @@ Fpp.seq [Fpp.newline, ppValue v]]

      | NIL =>
        Fpp.text "()"

  fun printVal (pos : Pos.t option, v : value) : unit=
    RedPrlLog.print RedPrlLog.INFO (pos, ppValue v)  
end
