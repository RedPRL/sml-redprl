structure MlSemantics : ML_SEMANTICS =
struct
  structure Syn = MlIntSyntax
  type term = Syn.term
  type jdg = Syn.jdg
  type metavariable = Syn.metavariable
  type metas = Syn.metas
  type syn_cmd = Syn.cmd

  structure Dict = SplayDict (structure Key = MlId)

  datatype value =
     THUNK of env * syn_cmd
   | THM of jdg * Tm.abs
   | DATA_INFO of term
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


  fun renameEnv (env : env) rho =
    let
      val rho' = Metavar.Ctx.map (fn X => Option.getOpt (Metavar.Ctx.find rho X, X)) (#2 env)
      val rho'' = Metavar.Ctx.union rho' rho (fn (_, X, _) => X)
    in
      (#1 env, rho'')
    end

  fun renameVal s ren =
    let
      fun go ren =
        fn THUNK (env, cmd) => THUNK (renameEnv env ren, cmd)
         | THM (jdg, abs) => THM (Sequent.map (Tm.renameMetavars ren) jdg, Tm.mapAbs (Tm.renameMetavars ren) abs)
         | TERM term => TERM (Tm.renameMetavars ren term)
         | ABS (METAS psi, s) => ABS (METAS psi, go (List.foldr (fn ((X, _), ren) => Metavar.Ctx.remove ren X) ren psi) s)
         | METAS psi => METAS (List.map (fn (X, vl) => (Option.getOpt (Metavar.Ctx.find ren X, X), vl)) psi)
         | NIL => NIL
         | DATA_INFO foo => DATA_INFO foo (* TODO *)
    in
      go ren s
    end

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
      | THM (jdg, abs) =>
        let
          val Tm.\ (_, abt) = Tm.outb abs
        in
          Fpp.seq
            [Fpp.text "Thm:",
            Fpp.nest 2 @@ Fpp.seq [Fpp.newline, Sequent.pretty jdg],
            Fpp.newline,
            Fpp.newline,
            Fpp.text "Extract:",
            Fpp.nest 2 @@ Fpp.seq [Fpp.newline, TermPrinter.ppTerm abt]]
        end

      | DATA_INFO _ =>
        Fpp.text "<data decl>"

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
end
