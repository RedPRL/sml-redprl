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
       PRINT of string
     | EXTRACT of string
     | QUIT

    datatype elt =
       DECL of string * decl * Pos.t
     | CMD of cmd * Pos.t

    type sign = elt list
  end

  (* external language *)
  structure ESyn =
    MlSyntax
      (type id = string type metavariable = string type jdg = ast type term = ast * sort)


  (* internal language *)
  structure ISyn =
    MlSyntax
      (type id = Res.id type metavariable = metavariable type jdg = AJ.jdg type term = Tm.abt)

  fun compileSrcCmd pos : Src.cmd  -> ESyn.cmd =
    fn Src.PRINT nm =>
       ESyn.PRINT (SOME pos, ESyn.VAR nm)

     | Src.EXTRACT nm =>
       ESyn.MATCH_ABS
         (ESyn.VAR nm,
          "psi",
          "thm",
          ESyn.MATCH_THM
            (ESyn.VAR "thm",
             "jdg",
             "tm",
              ESyn.PRINT
                (SOME pos,
                 ESyn.ABS
                   (ESyn.VAR "psi",
                    ESyn.VAR "tm"))))

     | Src.QUIT =>
       ESyn.ABORT

  fun compileSrcDecl (nm : string) : Src.decl -> ESyn.cmd =
    fn Src.DEF {arguments, sort, definiens} =>
       ESyn.NU (arguments, ESyn.RET (ESyn.ABS (ESyn.METAS arguments, ESyn.TERM (definiens, sort))))

     | Src.TAC {arguments, script} =>
       ESyn.NU (arguments, ESyn.RET (ESyn.ABS (ESyn.METAS arguments, ESyn.TERM (script, RedPrlSort.TAC))))

     | Src.THM {arguments, goal, script} =>
       ESyn.NU
         (arguments,
          ESyn.BIND
            (ESyn.REFINE (goal, (script, RedPrlSort.TAC)),
             nm,
             ESyn.RET (ESyn.ABS (ESyn.METAS arguments, ESyn.VAR nm))))


  val rec compileSrcSig : Src.sign -> ESyn.cmd =
    fn [] =>
       ESyn.RET ESyn.NIL

     | Src.CMD (c, pos) :: sign =>
       ESyn.BIND (compileSrcCmd pos c, "_", compileSrcSig sign)

     | Src.DECL (nm, decl, _) :: sign =>
       ESyn.BIND (compileSrcDecl nm decl, nm, compileSrcSig sign)
  
  (* semantic domain *)
  structure Sem =
  struct
    datatype value =
       THUNK of env * ISyn.cmd
     | THM of ajdg * abt
     | TERM of abt
     | ABS of value * value
     | METAS of ISyn.bindings
     | NIL

    withtype env = value StringListDict.dict

    datatype cmd = RET of value

    val initEnv = StringListDict.empty

    fun lookup (env : env) (nm : string) : value =
      case StringListDict.find env nm of
         SOME v => v
       | NONE => fail (NONE, Fpp.hsep [Fpp.text "Could not find value of", Fpp.text nm, Fpp.text "in environment"])

    fun extend (env : env) (nm : string) (v : value) : env =
      StringListDict.insert env nm v

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

  local
    structure O = RedPrlOperator and S = RedPrlSort
  in
    fun lookupArity (renv : Res.env) (pos : Pos.t option) (opid : string) : arity =
      case Res.lookupId renv pos opid of
         Ty.ABS (vls, Ty.TERM tau) => (vls, tau)
       | Ty.ABS (vls, Ty.THM tau) => (vls, tau)
       | _ => fail (pos, Fpp.hsep [Fpp.text "Could not infer arity for opid", Fpp.text opid])

    fun checkAbt pos (view, tau) : abt =
      Tm.setAnnotation pos @@ Tm.check (view, tau)
      handle exn =>
        fail (pos, Fpp.hsep [Fpp.text "Error resolving abt:", Fpp.text (exnMessage exn)])

    fun guessSort (renv : Res.env) (ast : ast) : sort =
      let
        val pos = Ast.getAnnotation ast
      in
        case Ast.out ast of
           Ast.` x =>
           #2 @@ Res.lookupVar renv pos x

         | Ast.$# (X, _) =>
           #2 o #2 @@ Res.lookupMeta renv pos X

         | Ast.$ (O.CUST (opid, _), _) =>
           #2 @@ lookupArity renv pos opid

         | Ast.$ (theta, _) =>
           (#2 @@ O.arity theta
            handle _ => fail (NONE, Fpp.text "Error guessing sort"))
      end

    fun resolveAjdg (renv : Res.env) (ast : ast) : ajdg =
      let
        val abt = resolveAst renv (ast, S.JDG)
      in
        AJ.out abt
        handle _ =>
          fail (NONE, Fpp.hsep [Fpp.text "Expected atomic judgment but got", TermPrinter.ppTerm abt])
      end

    and resolveAst (renv : Res.env) (ast : ast, tau : sort) : abt =
      let
        val pos = Ast.getAnnotation ast
      in
        case Ast.out ast of
           Ast.` x =>
           checkAbt pos (Tm.` o #1 @@ Res.lookupVar renv pos x, tau)

         | Ast.$# (X, asts : ast list) =>
           let
             val (X', (taus, _)) = Res.lookupMeta renv pos X
             val _ = 
               if List.length asts = List.length taus then () else 
                 fail (pos, Fpp.hsep [Fpp.text "Incorrect valence for metavariable", Fpp.text X])
             val abts = ListPair.map (resolveAst renv) (asts, taus)
           in
             checkAbt pos (Tm.$# (X', abts), tau)
           end

         | Ast.$ (theta, bs) =>
           let
             val theta' = resolveOpr renv pos theta bs
             val ar as (vls, tau) = O.arity theta'
             val _ =
               if List.length bs = List.length vls then () else
                 Err.raiseAnnotatedError' (pos, Err.INCORRECT_ARITY theta')
             val bs' = ListPair.map (resolveBnd renv) (vls, bs)
           in
             checkAbt pos (Tm.$ (theta', bs'), tau)
           end
      end

    and resolveBnd (renv : Res.env) ((taus, tau), Ast.\ (xs, ast)) : abt Tm.bview =
      let
        val (xs', renv') = Res.extendVars renv (xs, taus)
      in
        Tm.\ (List.map #1 xs', resolveAst renv' (ast, tau))
      end

    and resolveOpr (renv : Res.env) (pos : Pos.t option) (theta : O.operator) (bs : ast Ast.abs list) : O.operator =
      (case theta of
         O.CUST (opid, NONE) =>
         O.CUST (opid, SOME @@ lookupArity renv pos opid)

       | O.MK_ANY NONE =>
         let
           val [Ast.\ (_, ast)] = bs
         in
           O.MK_ANY o SOME @@ guessSort renv ast
         end

       | O.DEV_LET NONE =>
         let
           val [Ast.\ (_, jdg), _, _] = bs
         in
           O.DEV_LET o SOME o AJ.synthesis @@ resolveAjdg renv jdg
         end

       | th => th)
       handle _ =>
         fail (pos, Fpp.text "Error resolving operator")
  end

  fun resolveVal (renv : Res.env) : ESyn.value -> ISyn.value * Ty.vty =
    fn ESyn.THUNK cmd =>
       let
         val (cmd', cty) = resolveCmd renv cmd
       in
         (ISyn.THUNK cmd', Ty.DOWN cty)
       end

     | ESyn.VAR nm =>
       (ISyn.VAR nm, Res.lookupId renv NONE nm)

     | ESyn.NIL =>
       (ISyn.NIL, Ty.ONE)

     | ESyn.TERM (ast, tau) =>
       (ISyn.TERM @@ resolveAst renv (ast, tau), Ty.TERM tau)

     | ESyn.METAS psi =>
       let
         val psi' = (List.map (fn (X, vl) => Res.lookupMeta renv NONE X) psi)
         val vls = List.map #2 psi'
       in
         (ISyn.METAS psi', Ty.METAS vls)
       end

     | ESyn.ABS (vpsi, v) =>
       let
         val (vpsi', Ty.METAS vls) = resolveVal renv vpsi
         val (v', vty) = resolveVal renv v
       in
         (ISyn.ABS (vpsi', v'), Ty.ABS (vls, vty))
       end

  and resolveCmd (renv : Res.env) : ESyn.cmd -> ISyn.cmd * Ty.cty =
    fn ESyn.BIND (cmd1, nm, cmd2) =>
       let
         val (cmd1', Ty.UP vty1) = resolveCmd renv cmd1
         val (cmd2', cty2) = resolveCmd (Res.extendId renv nm vty1) cmd2
       in
         (ISyn.BIND (cmd1', nm, cmd2'), cty2)
       end

     | ESyn.RET v =>
       let
         val (v', vty) = resolveVal renv v
       in
         (ISyn.RET v', Ty.UP vty)
       end

     | ESyn.FORCE v =>
       let
         val (v', vty) = resolveVal renv v
       in
         case vty of
            Ty.DOWN cty => (ISyn.FORCE v', cty)
          | _ => fail (NONE, Fpp.text "Expected down-shifted type")
       end

     | ESyn.PRINT (pos, v) =>
       (ISyn.PRINT (pos, #1 @@ resolveVal renv v), Ty.UP Ty.ONE)

     | ESyn.REFINE (ajdg, script) =>
       let
         val ajdg' = resolveAjdg renv ajdg
         val script' = resolveAst renv script
       in
         (ISyn.REFINE (ajdg', script'), Ty.UP o Ty.THM @@ AJ.synthesis ajdg')
       end

     | ESyn.NU (psi, cmd) =>
       let
         val (psi', renv') = Res.extendMetas renv @@ ListPair.unzip psi
         val (cmd', cty) = resolveCmd renv' cmd
       in
         (ISyn.NU (psi', cmd'), cty)
       end

     | ESyn.MATCH_THM (v, xjdg, xtm, cmd) =>
       let
         val (v', ty) = resolveVal renv v
         val tau =
           case ty of
              Ty.THM tau => tau
            | _ => fail (NONE, Fpp.text "MATCH_THM applied to non-theorem")

         val renv' = Res.extendId renv xjdg @@ Ty.TERM RedPrlSort.JDG
         val renv'' = Res.extendId renv' xtm @@ Ty.TERM tau
         val (cmd', cty) = resolveCmd renv'' cmd
       in
         (ISyn.MATCH_THM (v', xjdg, xtm, cmd'), cty)
       end

     | ESyn.MATCH_ABS (v, xpsi, xv, cmd) =>
       let
         val (v', Ty.ABS (vls, vty)) = resolveVal renv v
         val renv' = Res.extendId renv xpsi @@ Ty.METAS vls
         val renv'' = Res.extendId renv' xv vty
         val (cmd', cty) = resolveCmd renv'' cmd
       in
         (ISyn.MATCH_ABS (v', xpsi, xv, cmd'), cty)
       end

     | ESyn.ABORT =>
       (ISyn.ABORT, Ty.UP Ty.ONE)
       (* ? *)

  structure MiniSig : MINI_SIGNATURE =
  struct
    type opid = string
    type abt = abt
    type sign = Sem.env

    fun makeSubst (psi, args) =
      ListPair.foldl
        (fn ((X, vl), bnd, rho) =>
          Tm.Metavar.Ctx.insert rho X @@ Tm.checkb (bnd, vl))
        Tm.Metavar.Ctx.empty
        (psi, args)

    fun isTheorem env opid =
      let
        val Sem.ABS (psi, s) = Sem.lookup env opid
      in
        case s of
           Sem.THM _ => true
         | _ => false
      end

    fun theoremSpec env opid args =
      let
        val Sem.ABS (Sem.METAS psi, Sem.THM (jdg, _)) = Sem.lookup env opid
        val rho = makeSubst (psi, args)
      in
        AJ.map (Tm.substMetaenv rho) jdg
      end
      handle Bind => fail (NONE, Fpp.text "internal error: theoremSpec caled on non-theorem")

    fun unfoldOpid env opid args =
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
      val (icmd, _) = resolveCmd Res.init ecmd
      val (scmd, exit) = evalCmd Sem.initEnv icmd
    in
      exit
    end
end
