structure MlEvaluate : ML_EVALUATE =
struct
  structure Sem = MlSemantics
  structure Syn = MlIntSyntax

  structure AJ = AtomicJudgment and Err = RedPrlError

  type env = Sem.env
  type syn_value = Syn.value
  type syn_cmd = Syn.cmd
  type sem_value = Sem.value
  type sem_cmd = Sem.cmd

  type abt = Tm.abt

  type exit_code = bool

  exception todo fun ?e = raise e
  fun @@ (f, x) = f x
  infixr @@


  structure MiniSig : MINI_SIGNATURE =
  struct
    type opid = MlId.t
    type abt = abt
    type sign = Sem.env

    fun makeSubst (psi, args) =
      ListPair.foldl
        (fn ((X, vl), bnd, rho) =>
          Tm.Metavar.Ctx.insert rho X @@ Tm.checkb (bnd, vl))
        Tm.Metavar.Ctx.empty
        (psi, args)

    fun isTheorem env (opid : MlId.t) =
      let
        val Sem.ABS (psi, s) = Sem.lookup env opid
      in
        case s of
           Sem.THM _ => true
         | _ => false
      end

    fun theoremSpec env (opid : MlId.t) args =
      let
        val Sem.ABS (Sem.METAS psi, Sem.THM (jdg, _)) = Sem.lookup env opid
        val Sequent.>> (hyps, ajdg) = jdg
        val _ = if Sequent.Hyps.isEmpty hyps then () else Err.raiseError @@ Err.GENERIC [Fpp.text "internal error: theoremSpec / expected empty hyps"]
        val rho = makeSubst (psi, args)
      in
        AJ.map (Tm.substMetaenv rho) ajdg
      end
      handle Bind =>
        Err.raiseError @@
          Err.GENERIC [Fpp.text "internal error: theoremSpec caled on non-theorem"]

    (* TODO *)
    fun dataDeclInfo env (opid : MlId.t) =
      ()

    fun unfoldOpid env (opid : MlId.t) args =
      let
        val Sem.ABS (Sem.METAS psi, s) = Sem.lookup env opid
        val rho = makeSubst (psi, args)
        val abt =
          case s of
             Sem.TERM abt => abt
           | Sem.THM (_, abs) =>
             let
               val Tm.\ (xs, abt) = Tm.outb abs
             in
               case xs of
                  [] => abt
                | _ => Err.raiseError @@ Err.GENERIC [Fpp.text "internal error: unfoldOpid called on non-atomic judgment"]
             end
           | _ => Err.raiseError @@ Err.GENERIC [Fpp.text "internal error: unfoldOpid called on something that cannot be unfolded"]
      in
        Tm.substMetaenv rho abt
      end
  end

  structure TacticElaborator = TacticElaborator (MiniSig)

  fun evalCmd (env : Sem.env) : Syn.cmd -> Sem.cmd * exit_code =
    fn Syn.BIND (cmd1, x, cmd2) =>
       let
         val (Sem.RET s1, ex1) = evalCmd env cmd1
         val (s2, ex2) = evalCmd (Sem.extend env x s1) cmd2
       in
         (s2, ex1 andalso ex2)
       end

     | Syn.RET v =>
       (Sem.RET @@ evalVal env v, true)

     | Syn.FORCE v =>
       (case evalVal env v of
           Sem.THUNK (env', cmd) => evalCmd env' cmd
         | _ => Err.raiseError @@ Err.GENERIC [Fpp.text "evalCmd/FORCE expected THUNK"])

     | Syn.FN (x, _, cmd) =>
       (Sem.FN (env, x, cmd), true)

     | Syn.AP (cmd, v) =>
       (case evalCmd env cmd of
           (Sem.FN (env', x, cmd'), ex) =>
           let
             val sv = evalVal env v
             val (s, ex') = evalCmd (Sem.extend env' x sv) cmd'
           in
             (s, ex andalso ex')
           end
         | _ =>
           Err.raiseError @@ Err.GENERIC [Fpp.text "evalCmd/AP expected FN"])

     | Syn.PRINT (pos, v) =>
       (RedPrlLog.print RedPrlLog.INFO (pos, Sem.ppValue (evalVal env v));
        (Sem.RET Sem.NIL, true))

     | Syn.REFINE (name, sequent, script) =>
       let
         val pos = Tm.getAnnotation script
         val sequent' = Sequent.map (Sem.term env) sequent
         val script' = Sem.term env script

         val results = TacticElaborator.tactic env Var.Ctx.empty script' sequent'

         (* TODO: somehow show all the states! *)
         val Lcf.|> (subgoals, evd) =
           Lcf.M.run (results, fn Lcf.|> (psi, _) => Lcf.Tl.isEmpty psi)
           handle _ => Lcf.M.run (results, fn _ => true)

         val {ren, ...} =
          Lcf.Tl.foldl
            (fn (x, Lcf.::@ (tr, jdg), {subgoals', ren, idx}) =>
              let
                val x' = Metavar.named (case name of SOME s => s ^ "/" ^ Int.toString idx | NONE => Int.toString idx)
                val jdg' = Lcf.J.ren ren jdg
                val ren' = Metavar.Ctx.insert ren x x'
              in
                {subgoals' = Lcf.Tl.snoc subgoals' x' jdg',
                 ren = ren',
                 idx = idx + 1}
              end)
            {subgoals' = Lcf.Tl.empty, ren = Metavar.Ctx.empty, idx = 0}
            subgoals

         val subgoalsCount = Lcf.Tl.foldl (fn (_, _, n) => n + 1) 0 subgoals
         val check =
           if subgoalsCount = 0 then () else
             RedPrlLog.print RedPrlLog.WARN (pos, Fpp.hsep [Fpp.text @@ Int.toString subgoalsCount, Fpp.text "Remaining Obligations"])
        in
          (Sem.RET @@ Sem.THM (sequent', Tm.mapAbs (Tm.renameMetavars ren) evd), subgoalsCount = 0)
        end

     | Syn.FRESH vls =>
       let
         val psi = List.map (fn (SOME name, vl) => (Metavar.named name, vl) | (NONE, vl) => (Metavar.new (), vl)) vls
       in
         (Sem.RET @@ Sem.METAS psi, true)
       end

     | Syn.MATCH_METAS (v, Xs, cmd) =>
       (case evalVal env v of
           Sem.METAS psi =>
           let
             val rho = ListPair.foldl (fn (X, (Y, _), rho) => Metavar.Ctx.insert rho X Y) Metavar.Ctx.empty (Xs, psi)
             val env' = Sem.renameEnv env rho
           in
             evalCmd env' cmd
           end
         | _ =>
           Err.raiseError @@ Err.GENERIC [Fpp.text "evalCmd/MATCH_METAS expected METAS"])

     | Syn.MATCH_THM (vthm, xjdg, xtm, cmd) =>
       (case evalVal env vthm of
           Sem.THM (jdg, abs) =>
           let
             val Sequent.>> (hyps, ajdg) = jdg
             val _ = if Sequent.Hyps.isEmpty hyps then () else Err.raiseError @@ Err.GENERIC [Fpp.text "MATCH_THM called on non-atomic theorem"]
             val Tm.\ (_, abt) = Tm.outb abs
             val env' = Sem.extend env xjdg @@ Sem.TERM @@ Sem.term env @@ AJ.into ajdg
             val env'' = Sem.extend env xtm @@ Sem.TERM @@ Sem.term env abt
           in
             evalCmd env'' cmd
           end
         | _ =>
           Err.raiseError @@ Err.GENERIC [Fpp.text "evalCmd/MATCH_THM expected THM"])

     | Syn.MATCH_ABS (vabs, xpsi, xv, cmd) =>
       (case evalVal env vabs of
           Sem.ABS (Sem.METAS psi, s) =>
           let
             val psi' = List.map (fn (X, vl) => (Metavar.named (Metavar.toString X), vl)) psi
             val ren = ListPair.foldlEq (fn ((X, _), (Y, _), rho) => Metavar.Ctx.insert rho X Y) Metavar.Ctx.empty (psi, psi')
             val env' = Sem.extend env xpsi @@ Sem.METAS psi'
             val env'' = Sem.extend env' xv @@ Sem.renameVal s ren
           in
             evalCmd env'' cmd
           end
         | _ =>
           Err.raiseError @@ Err.GENERIC [Fpp.text "evalCmd/MATCH_ABS expected ABS"])

     | Syn.ABORT =>
       Err.raiseError @@ Err.GENERIC [Fpp.text "Signature aborted"]

  and evalVal (env : Sem.env) : Syn.value -> Sem.value =
    fn Syn.THUNK cmd =>
       Sem.THUNK (env, cmd)

     | Syn.VAR nm =>
       Sem.lookup env nm

     | Syn.NIL =>
       Sem.NIL

     | Syn.ABS (vpsi, v) =>
       Sem.ABS (evalVal env vpsi, evalVal env v)

     | Syn.METAS psi =>
       Sem.METAS @@ List.map (fn (X, vl) => (Sem.lookupMeta env X, vl)) psi

     | Syn.TERM abt =>
       Sem.TERM (Sem.term env abt)

end
