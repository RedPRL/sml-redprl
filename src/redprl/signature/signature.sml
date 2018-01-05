structure Signature : SIGNATURE =
struct
  structure Ast = RedPrlAst and Tm = RedPrlAbt and AJ = AtomicJudgment and Err = RedPrlError

  type ast = Ast.ast
  type sort = RedPrlSort.t
  type arity = Tm.O.Ar.t
  type abt = Tm.abt
  type ajdg = AJ.jdg
  type valence = Tm.valence
  type metavariable = Tm.metavariable

  exception todo
  fun ?e = raise e

  structure Ty = MlType

  fun @@ (f, x) = f x
  infixr @@

  fun fail (pos, msg) =
    Err.raiseAnnotatedError' (pos, Err.GENERIC [msg])

  (* The resolver environment *)
  structure Res = MlResolver (Ty)

  structure Src =
  struct
    type arguments = (string * Tm.valence) list

    datatype decl =
       DEF of {arguments : arguments, sort : sort, definiens : ast}
     | THM of {arguments : arguments, goal : ast, script : ast}
     | TAC of {arguments : arguments, script : ast}

    datatype cmd =
       PRINT of MlId.t
     | EXTRACT of MlId.t
     | QUIT

    datatype elt =
       DECL of MlId.t * decl * Pos.t
     | CMD of cmd * Pos.t

    type sign = elt list
  end

  (* external language *)
  structure ESyn =
    MlSyntax
      (type id = MlId.t type metavariable = string type jdg = ast type term = ast * sort type vty = Ty.vty)


  (* internal language *)
  structure ISyn =
    MlSyntax
      (type id = MlId.t type metavariable = metavariable type jdg = AJ.jdg type term = Tm.abt type vty = Ty.vty)

  fun compileSrcCmd pos : Src.cmd  -> ESyn.cmd =
    fn Src.PRINT nm =>
       ESyn.PRINT (SOME pos, ESyn.VAR nm)

     | Src.EXTRACT nm =>
       (* pm nm as [Ψ].thm in
          pm thm as (jdg, tm) in
          print [Ψ].tm *)
       let
         val psi = MlId.new ()
         val thm = MlId.new ()
         val jdg = MlId.new ()
         val tm = MlId.new ()
       in
        ESyn.MATCH_ABS
          (ESyn.VAR nm,
            psi,
            thm,
            ESyn.MATCH_THM
              (ESyn.VAR thm,
              jdg,
              tm,
                ESyn.PRINT
                  (SOME pos,
                  ESyn.ABS
                    (ESyn.VAR psi,
                      ESyn.VAR tm))))
       end

     | Src.QUIT =>
       ESyn.ABORT

  val compileSrcDecl : Src.decl -> ESyn.cmd =
    fn Src.DEF {arguments, sort, definiens} =>
       (* ν arguments in ret [arguments].`definiens *)
       ESyn.NU (arguments, ESyn.RET (ESyn.ABS (ESyn.METAS arguments, ESyn.TERM (definiens, sort))))

     | Src.TAC {arguments, script} => 
       (* ν arguments in ret [arguments].`script *)
       ESyn.NU (arguments, ESyn.RET (ESyn.ABS (ESyn.METAS arguments, ESyn.TERM (script, RedPrlSort.TAC))))

     | Src.THM {arguments, goal, script} =>
       (* ν arguments in
          let x = refine goal script in
          ret [arguments].x *)     
       let
         val x = MlId.new ()
       in
         ESyn.NU
           (arguments,
            ESyn.BIND
              (ESyn.REFINE (goal, (script, RedPrlSort.TAC)),
               x,
               ESyn.RET (ESyn.ABS (ESyn.METAS arguments, ESyn.VAR x))))
        end

  val rec compileSrcSig : Src.sign -> ESyn.cmd =
    fn [] =>
       ESyn.RET ESyn.NIL

     | Src.CMD (c, pos) :: sign =>
       ESyn.BIND (compileSrcCmd pos c, MlId.new (), compileSrcSig sign)

     | Src.DECL (nm, decl, _) :: sign =>
       ESyn.BIND (compileSrcDecl decl, nm, compileSrcSig sign)
  
  
  structure Sem = MlSemantics (ISyn)

  structure ElabKit = 
  struct
    structure R = Res and Ty = Ty and ESyn = ESyn and ISyn = ISyn
  end

  structure Elab = MlElaborate (ElabKit)


  (* TODO: move what follows into a new module MlEvaluate : ML_EVALUATE *)
  
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
        val rho = makeSubst (psi, args)
      in
        AJ.map (Tm.substMetaenv rho) jdg
      end
      handle Bind => fail (NONE, Fpp.text "internal error: theoremSpec caled on non-theorem")

    fun unfoldOpid env (opid : MlId.t) args =
      let
        val Sem.ABS (Sem.METAS psi, s) = Sem.lookup env opid
        val rho = makeSubst (psi, args)
        val abt =
          case s of
             Sem.TERM abt => abt
           | Sem.THM (_, abt) => abt
           | _ => fail (NONE, Fpp.text "internal error: unfoldOpid called on something that cannot be unfolded")
      in
        Tm.substMetaenv rho abt
      end
  end

  structure TacticElaborator = TacticElaborator (MiniSig)
  type exit_code = bool

  fun evalCmd (env : Sem.env) : ISyn.cmd -> Sem.cmd * exit_code =
    fn ISyn.BIND (cmd1, x, cmd2) =>
       let
         val (Sem.RET s1, ex1) = evalCmd env cmd1
         val (s2, ex2) = evalCmd (Sem.extend env x s1) cmd2
       in
         (s2, ex1 andalso ex2)
       end

     | ISyn.RET v =>
       (Sem.RET @@ evalVal env v, true)

     | ISyn.FORCE v =>
       (case evalVal env v of
           Sem.THUNK (env', cmd) => evalCmd env' cmd
         | _ => fail (NONE, Fpp.text "evalCmd/ISyn.FORCE expected Sem.THUNK"))

     | ISyn.FN (x, _, cmd) =>
       (Sem.FN (env, x, cmd), true)

     | ISyn.AP (cmd, v) =>
       (case evalCmd env cmd of
           (Sem.FN (env', x, cmd'), ex) => 
           let
             val sv = evalVal env v
             val (s, ex') = evalCmd (Sem.extend env' x sv) cmd'
           in
             (s, ex andalso ex')
           end
         | _ => fail (NONE, Fpp.text "evalCmd/ISyn.AP expected Sem.FN"))

     | ISyn.PRINT (pos, v) =>
       (Sem.printVal (pos, evalVal env v);
        (Sem.RET Sem.NIL, true))

     | ISyn.REFINE (ajdg, script) =>
       let
         val pos = Tm.getAnnotation script
         val seqjdg = Sequent.>> (SequentData.Hyps.empty, ajdg)
         val results = TacticElaborator.tactic env Var.Ctx.empty script (fn _ => Sym.new ()) seqjdg
         (* TODO: somehow show all the states! *)
         val Lcf.|> (subgoals, evd) =
           Lcf.M.run (results, fn Lcf.|> (psi, _) => Lcf.Tl.isEmpty psi)
           handle _ => Lcf.M.run (results, fn _ => true)

         val Tm.\ (_, extract) = Tm.outb evd
         val subgoalsCount = Lcf.Tl.foldl (fn (_, _, n) => n + 1) 0 subgoals

         val check =
           if subgoalsCount = 0 then () else
             RedPrlLog.print RedPrlLog.WARN (pos, Fpp.hsep [Fpp.text @@ Int.toString subgoalsCount, Fpp.text "Remaining Obligations"])
        in
          (Sem.RET @@ Sem.THM (ajdg, extract), subgoalsCount = 0)
        end

     | ISyn.NU (psi, cmd) =>
       evalCmd env cmd

     | ISyn.MATCH_THM (vthm, xjdg, xtm, cmd) =>
       (case evalVal env vthm of
           Sem.THM (jdg, abt) =>
           let
             val env' = Sem.extend env xjdg @@ Sem.TERM @@ AJ.into jdg
             val env'' = Sem.extend env xtm @@ Sem.TERM abt
           in
             evalCmd env'' cmd
           end
         | _ => fail (NONE, Fpp.text "evalCmd/ISyn.MATCH_THM expected Sem.THM"))

     | ISyn.MATCH_ABS (vabs, xpsi, xv, cmd) =>
       (case evalVal env vabs of
           Sem.ABS (spsi, s) =>
           let
             val env' = Sem.extend env xpsi spsi
             val env'' = Sem.extend env' xv s
             (* TODO: this should freshen! *)
           in
             evalCmd env'' cmd
           end
         | _ => fail (NONE, Fpp.text "evalCmd/ISyn.MATCH_ABS expected Sem.ABS"))

     | ISyn.ABORT =>
       fail (NONE, Fpp.text "Signature aborted")

  and evalVal (env : Sem.env) : ISyn.value -> Sem.value =
    fn ISyn.THUNK cmd =>
       Sem.THUNK (env, cmd)

     | ISyn.VAR nm =>
       Sem.lookup env nm

     | ISyn.NIL =>
       Sem.NIL

     | ISyn.ABS (psi, v) =>
       Sem.ABS (evalVal env psi, evalVal env v)

     | ISyn.METAS psi =>
       Sem.METAS psi

     | ISyn.TERM abt =>
       Sem.TERM abt

  structure L = RedPrlLog

  fun checkSrcSig (sign : Src.sign) : bool =
    let
      val ecmd = compileSrcSig sign
      val (icmd, _) = Elab.elabCmd Res.init ecmd
      val (scmd, exit) = evalCmd Sem.initEnv icmd
    in
      exit
    end
end
