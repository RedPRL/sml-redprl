structure SignatureNew = 
struct
  structure Ast = RedPrlAst and Tm = RedPrlAbt and AJ = AtomicJudgment

  type ast = Ast.ast
  type sort = RedPrlSort.t
  type arity = Tm.O.Ar.t
  type abt = Tm.abt
  type ajdg = AJ.jdg

  exception todo
  fun ?e = raise e

  structure Ty = 
  struct
    datatype vty =
       ONE
     | DOWN of cty
     | TERM of sort
     | THM of sort
     | ABS of Tm.valence list * vty

    and cty = 
       UP of vty
  end

  fun @@ (f, x) = f x
  infixr @@

  fun fail (pos, msg) = 
    RedPrlError.raiseError @@
      RedPrlError.GENERIC [msg]

  (* The resolver environment *)
  structure Res :>
  sig
    type env

    val init : env

    val lookupId : env -> Pos.t option -> string -> Ty.vty
    val extendId : env -> string -> Ty.vty -> env

    val lookupVar : env -> Pos.t option -> string -> (Tm.variable * Tm.sort)
    val lookupMeta : env -> Pos.t option -> string -> (Tm.metavariable * Tm.valence)

    val extendVars : env -> string list * Tm.sort list -> ((Tm.variable * Tm.sort) list * env)
    val extendMetas : env -> string list * Tm.valence list -> ((Tm.metavariable * Tm.valence) list * env)
  end = 
  struct
    type env =
      {ids : Ty.vty StringListDict.dict,
       vars : (Tm.variable * Tm.sort) StringListDict.dict,
       metas : (Tm.metavariable * Tm.valence) StringListDict.dict}

    val init = 
      {ids = StringListDict.empty,
       vars = StringListDict.empty,
       metas = StringListDict.empty}

    fun lookup dict pos x = 
      case StringListDict.find dict x of 
         SOME r => r
       | NONE => fail (pos, Fpp.hsep [Fpp.text "Could not resolve name", Fpp.text x])
      
    fun lookupId (env : env) =
      lookup (#ids env)

    fun lookupVar (env : env) =
      lookup (#vars env)
      
    fun lookupMeta (env : env) =
      lookup (#metas env)      

    (* TODO: ensure that this name is not already used *)
    fun extendId {ids, vars, metas} nm vty =
      {ids = StringListDict.insert ids nm vty,
       vars = vars,
       metas = metas}

    fun extendVars {ids, vars, metas} (xs, taus) =
      let
        val (gamma, vars') =
          ListPair.foldrEq
            (fn (x, tau, (gamma, vars)) =>
              let
                val x' = Sym.named x
              in
                ((x',tau) :: gamma, StringListDict.insert vars x (x', tau))
              end)
            ([], vars)
            (xs, taus)
        val env = {ids = ids, vars = vars', metas = metas}
      in    
        (gamma, env)
      end
      handle exn =>
        fail (NONE, Fpp.hsep [Fpp.text "extendVars: invalid arguments,", Fpp.text (exnMessage exn)])

    fun extendMetas {ids, vars, metas} (Xs, vls) =
      let
        val (psi, metas') =
          ListPair.foldrEq
            (fn (X, vl, (psi, metas)) =>
              let
                val X' = Metavar.named X
              in
                ((X',vl) :: psi, StringListDict.insert metas X (X', vl))
              end)
            ([], metas)
            (Xs, vls)
        val env = {ids = ids, vars = vars, metas = metas'}
      in
        (psi, env)
      end
      handle _ =>
        fail (NONE, Fpp.text "extendMetas: invalid arguments")
  end

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

    datatype elt = 
       DECL of string * decl * Pos.t
     | CMD of cmd * Pos.t

    type sign = elt list
  end

  (* external language *)
  structure ESyn =
  struct
    datatype value = 
       THUNK of cmd
     | VAR of string
     | NIL
     | ABS of (string * Tm.valence) list * value
     | TERM of ast * sort

    and cmd = 
       BIND of cmd * string * cmd
     | RET of value
     | FORCE of value
     | PRINT of Pos.t option * value
     | REFINE of ast * ast
     | NU of (string * Tm.valence) list * cmd

    fun compileSrcCmd pos : Src.cmd  -> cmd =
      fn Src.PRINT nm => PRINT (SOME pos, VAR nm)
       | Src.EXTRACT nm => PRINT (SOME pos, VAR nm) (* TODO *)

    fun compileSrcDecl (nm : string) : Src.decl -> cmd = 
      fn Src.DEF {arguments, sort, definiens} =>
         RET (ABS (arguments, TERM (definiens, sort)))

       | Src.TAC {arguments, script} =>
         RET (ABS (arguments, TERM (script, RedPrlSort.TAC)))

       | Src.THM {arguments, goal, script} =>
         NU (arguments, BIND (REFINE (goal, script), nm, RET (ABS (arguments, VAR nm))))

    val rec compileSrcSig : Src.sign -> cmd = 
      fn [] => 
         RET NIL
    
       | Src.CMD (c, pos) :: sign =>
         BIND (compileSrcCmd pos c, "_", compileSrcSig sign)
        
       | Src.DECL (nm, decl, _) :: sign =>
         BIND (compileSrcDecl nm decl, nm, compileSrcSig sign)
  end

  (* internal language *)
  structure ISyn =
  struct
    datatype value = 
       THUNK of cmd
     | VAR of string
     | NIL
     | ABS of (Tm.metavariable * Tm.valence) list * value
     | TERM of abt

    and cmd = 
       BIND of cmd * string * cmd
     | RET of value
     | FORCE of value
     | PRINT of Pos.t option * value
     | REFINE of ajdg * abt
     | NU of (Tm.metavariable * Tm.valence) list * cmd
  end

  (* semantic domain *)
  structure Sem = 
  struct
    datatype value = 
       THUNK of env * ISyn.cmd
     | THM of ajdg * abt
     | TERM of abt
     | ABS of (Tm.metavariable * Tm.valence) list * value
     | NIL

    withtype env = value StringListDict.dict * Tm.metavariable Tm.Metavar.Ctx.dict

    datatype cmd = RET of value

    val initEnv = (StringListDict.empty, Tm.Metavar.Ctx.empty)

    fun lookup (env : env) (nm : string) : value =
      case StringListDict.find (#1 env) nm of 
         SOME v => v
       | NONE => fail (NONE, Fpp.hsep [Fpp.text "Could not find value of", Fpp.text nm, Fpp.text "in environment"])

    fun extend (env : env) (nm : string) (v : value) : env =
      (StringListDict.insert (#1 env) nm v, #2 env)

    fun freshenMetas (env : env) (psi : (Tm.metavariable * Tm.valence) list) : env = 
      let
        val clone = Tm.Metavar.named o Tm.Metavar.toString
        val rho = List.foldl (fn ((X, _), rho) => Tm.Metavar.Ctx.insert rho X (clone X)) (#2 env) psi      
      in
        (#1 env, rho)
      end

    (* TODO *)
    val rec ppValue : value -> Fpp.doc = 
      fn THUNK _ => Fpp.text "<thunk>"
       | THM (jdg, abt) =>
         Fpp.seq
           [Fpp.text "Theorem",
            Fpp.newline,
            Fpp.nest 2 @@ Fpp.seq [Fpp.newline, AJ.pretty jdg],
            Fpp.newline,
            Fpp.newline,
            Fpp.text "ext",
            Fpp.newline,
            Fpp.nest 2 @@ Fpp.seq [Fpp.newline, TermPrinter.ppTerm abt]]

       | TERM abt => TermPrinter.ppTerm abt
       | ABS (psi, v) =>
         Fpp.seq
           [Fpp.hsep
            [Fpp.collection
              (Fpp.char #"[")
              (Fpp.char #"]")
              Fpp.Atomic.comma
              (List.map (fn (X, vl) => Fpp.hsep [TermPrinter.ppMeta X, Fpp.Atomic.colon, TermPrinter.ppValence vl]) psi),
             Fpp.text "=>"],
            Fpp.nest 2 @@ Fpp.seq [Fpp.newline, ppValue v]]
       | NIL => Fpp.text "()"

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
       | _ => fail (NONE, Fpp.hsep [Fpp.text "Could not infer arity for opid", Fpp.text opid])

    fun checkAbt (view, tau) : abt =
      Tm.check (view, tau)
      handle exn => 
        fail (NONE, Fpp.hsep [Fpp.text "Error resolving abt:", Fpp.text (exnMessage exn)])

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
        Tm.setAnnotation pos
        (case Ast.out ast of 
           Ast.` x =>
           checkAbt (Tm.` o #1 @@ Res.lookupVar renv pos x, tau)

         | Ast.$# (X, asts : ast list) =>
           let
             val (X', (taus, _)) = Res.lookupMeta renv pos X
             val abts = ListPair.mapEq (resolveAst renv) (asts, taus)
           in
             checkAbt (Tm.$# (X', abts), tau)
           end

         | Ast.$ (theta, bs) =>
           let
             val theta' = resolveOpr renv pos theta bs
             val (vls, tau) = O.arity theta'
             val bs' = ListPair.mapEq (resolveBnd renv) (vls, bs)
           in
             checkAbt (Tm.$ (theta', bs'), tau)
           end)
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

       | O.DEV_APPLY_LEMMA (opid, NONE, pat) => 
         O.DEV_APPLY_LEMMA (opid, SOME @@ lookupArity renv pos opid, pat)

       | O.DEV_USE_LEMMA (opid, NONE) =>
         O.DEV_USE_LEMMA (opid, SOME @@ lookupArity renv pos opid)

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

     | ESyn.ABS (psi, v) =>
       let
         val (psi', renv') = Res.extendMetas renv @@ ListPair.unzip psi
         val (v', vty) = resolveVal renv' v
       in
         (ISyn.ABS (psi', v'), Ty.ABS (List.map #2 psi', vty))
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
         val script' = resolveAst renv (script, RedPrlSort.TAC)
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


  structure MiniSig : MINI_SIGNATURE = 
  struct
    type opid = string
    type abt = abt
    type sign = Sem.env

    fun opidSpec env opid args = ?todo
    fun unfoldOpid env opid args = ?todo
  end

  structure TacticElaborator = TacticElaborator (MiniSig)
  
  fun evalCmd (env : Sem.env) : ISyn.cmd -> Sem.cmd =
    fn ISyn.BIND (cmd1, x, cmd2) =>
       let
         val Sem.RET s = evalCmd env cmd1
       in
         evalCmd (Sem.extend env x s) cmd2
       end

     | ISyn.RET v => 
       Sem.RET @@ evalVal env v

     | ISyn.FORCE v =>
       (case evalVal env v of 
           Sem.THUNK (env', cmd) => evalCmd env' cmd
         | _ => fail (NONE, Fpp.text "evalCmd/ISyn.FORCE expected Sem.THUNK"))

     | ISyn.PRINT (pos, v) =>
       (Sem.printVal (pos, evalVal env v);
        Sem.RET Sem.NIL)

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
         val warning = 
           if subgoalsCount = 0 then () else
             RedPrlLog.print RedPrlLog.WARN (pos, Fpp.hsep [Fpp.text @@ Int.toString subgoalsCount, Fpp.text "Remaining Obligations"])

          val mrho = #2 env
          val ajdg' = AJ.map (Tm.renameMetavars mrho) ajdg
          val extract' = Tm.renameMetavars mrho extract
        in
          Sem.RET @@ Sem.THM (ajdg', extract')
        end
    
     | ISyn.NU (psi, cmd) =>
       evalCmd (Sem.freshenMetas env psi) cmd

  and evalVal (env : Sem.env) : ISyn.value -> Sem.value =
    fn ISyn.THUNK cmd => 
       Sem.THUNK (env, cmd)

     | ISyn.VAR nm =>
       Sem.lookup env nm

     | ISyn.NIL =>
       Sem.NIL

     | ISyn.ABS (psi, v) =>
       Sem.ABS (psi, evalVal env v)

     | ISyn.TERM abt =>
       Sem.TERM (Tm.renameMetavars (#2 env) abt)
     
  structure L = RedPrlLog

  fun check (sign : Src.sign) : bool = 
    let
      val ecmd = ESyn.compileSrcSig sign
      val (icmd, _) = resolveCmd Res.init ecmd
      val scmd = evalCmd Sem.initEnv icmd
    in
      true
    end
end
