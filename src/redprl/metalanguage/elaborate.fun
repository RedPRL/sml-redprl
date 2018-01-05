signature ML_ELAB_KIT = 
sig
  structure Ty : ML_TYPE

  structure R : RESOLVER
    where type id = MlId.t
    where type mltype = Ty.vty

  structure ESyn : ML_SYNTAX
    where type term = RedPrlAst.ast * Tm.sort
    where type vty = Ty.vty
    where type id = MlId.t
    where type metavariable = string
    where type jdg = RedPrlAst.ast
  
  structure ISyn : ML_SYNTAX
    where type term = Tm.abt
    where type vty = Ty.vty
    where type id = MlId.t
    where type metavariable = Tm.metavariable
    where type jdg = AtomicJudgment.jdg
end

functor MlElaborate (Kit : ML_ELAB_KIT) : ML_ELABORATE = 
struct
  open Kit
  
  type env = R.env
  type ivalue = ISyn.value
  type icmd = ISyn.cmd
  type evalue = ESyn.value
  type ecmd = ESyn.cmd
  type vty = Ty.vty
  type cty = Ty.cty

  structure Ast = RedPrlAst and AJ = AtomicJudgment
  type ast = Ast.ast
  type abt = Tm.abt
  type sort = Tm.sort

  exception todo fun ?e = raise e
  fun @@ (f, x) = f x
  infixr @@


  structure O = RedPrlOperator and S = RedPrlSort and Err = RedPrlError
  type arity = O.Ar.t


  fun lookupArity (env : env) (pos : Pos.t option) (opid : MlId.t) : arity =
    case R.lookupId env pos opid of
        Ty.ABS (vls, Ty.TERM tau) => (vls, tau)
      | Ty.ABS (vls, Ty.THM tau) => (vls, tau)
      | _ => Err.raiseAnnotatedError' (pos, Err.GENERIC [Fpp.text "Could not infer arity for opid", Fpp.text (MlId.toString opid)])

  fun checkAbt pos (view, tau) : abt =
    Tm.setAnnotation pos @@ Tm.check (view, tau)
    handle exn =>
      Err.raiseAnnotatedError' (pos, Err.GENERIC [Fpp.text "Error resolving abt:", Fpp.text (exnMessage exn)])

  fun guessSort (env : env) (ast : ast) : sort =
    let
      val pos = Ast.getAnnotation ast
    in
      case Ast.out ast of
          Ast.` x =>
          #2 @@ R.lookupVar env pos x

        | Ast.$# (X, _) =>
          #2 o #2 @@ R.lookupMeta env pos X

        | Ast.$ (O.CUST (opid, _), _) =>
          #2 @@ lookupArity env pos opid

        | Ast.$ (theta, _) =>
          (#2 @@ O.arity theta
          handle _ => Err.raiseError @@ Err.GENERIC [Fpp.text "Error guessing sort"])
    end

  fun elabAtomicJdg (env : env) (ast : ast) : AJ.jdg =
    let
      val abt = elabAst env (ast, S.JDG)
    in
      AJ.out abt
      handle _ =>
        Err.raiseError @@ Err.GENERIC [Fpp.text "Expected atomic judgment but got", TermPrinter.ppTerm abt]
    end

  and elabAst (env : env) (ast : ast, tau : sort) : abt =
    let
      val pos = Ast.getAnnotation ast
    in
      case Ast.out ast of
          Ast.` x =>
          checkAbt pos (Tm.` o #1 @@ R.lookupVar env pos x, tau)

        | Ast.$# (X, asts : ast list) =>
          let
            val (X', (taus, _)) = R.lookupMeta env pos X
            val _ = 
              if List.length asts = List.length taus then () else 
                Err.raiseAnnotatedError' (pos, Err.GENERIC [Fpp.text "Incorrect valence for metavariable", Fpp.text X])
            val abts = ListPair.map (elabAst env) (asts, taus)
          in
            checkAbt pos (Tm.$# (X', abts), tau)
          end

        | Ast.$ (theta, bs) =>
          let
            val theta' = elabOpr env pos theta bs
            val ar as (vls, tau) = O.arity theta'
            val _ =
              if List.length bs = List.length vls then () else
                Err.raiseAnnotatedError' (pos, Err.INCORRECT_ARITY theta')
            val bs' = ListPair.map (elabBnd env) (vls, bs)
          in
            checkAbt pos (Tm.$ (theta', bs'), tau)
          end
    end

  and elabBnd (env : env) ((taus, tau), Ast.\ (xs, ast)) : abt Tm.bview =
    let
      val (xs', env') = R.extendVars env (xs, taus)
    in
      Tm.\ (List.map #1 xs', elabAst env' (ast, tau))
    end

  and elabOpr (env : env) (pos : Pos.t option) (theta : O.operator) (bs : ast Ast.abs list) : O.operator =
    (case theta of
        O.CUST (opid, NONE) =>
        O.CUST (opid, SOME @@ lookupArity env pos opid)

      | O.MK_ANY NONE =>
        let
          val [Ast.\ (_, ast)] = bs
        in
          O.MK_ANY o SOME @@ guessSort env ast
        end

      | O.DEV_LET NONE =>
        let
          val [Ast.\ (_, jdg), _, _] = bs
        in
          O.DEV_LET o SOME o AJ.synthesis @@ elabAtomicJdg env jdg
        end

      | th => th)
      handle _ =>
        Err.raiseAnnotatedError' (pos, Err.GENERIC @@ [Fpp.text "Error resolving operator"])


  fun elabValue (env : R.env) : ESyn.value -> ISyn.value * Ty.vty =
    fn ESyn.THUNK cmd =>
       let
         val (cmd', cty) = elabCmd env cmd
       in
         (ISyn.THUNK cmd', Ty.DOWN cty)
       end

     | ESyn.VAR nm =>
       (ISyn.VAR nm, R.lookupId env NONE nm)

     | ESyn.NIL =>
       (ISyn.NIL, Ty.ONE)

     | ESyn.TERM (ast, tau) =>
       (ISyn.TERM @@ elabAst env (ast, tau), Ty.TERM tau)

     | ESyn.METAS psi =>
       let
         val psi' = (List.map (fn (X, vl) => R.lookupMeta env NONE X) psi)
         val vls = List.map #2 psi'
       in
         (ISyn.METAS psi', Ty.METAS vls)
       end

     | ESyn.ABS (vpsi, v) =>
       let
         val (vpsi', Ty.METAS vls) = elabValue env vpsi
         val (v', vty) = elabValue env v
       in
         (ISyn.ABS (vpsi', v'), Ty.ABS (vls, vty))
       end

  and elabCmd (env : env) : ESyn.cmd -> ISyn.cmd * Ty.cty =
    fn ESyn.BIND (cmd1, nm, cmd2) =>
       let
         val (cmd1', Ty.UP vty1) = elabCmd env cmd1
         val (cmd2', cty2) = elabCmd (R.extendId env nm vty1) cmd2
       in
         (ISyn.BIND (cmd1', nm, cmd2'), cty2)
       end

     | ESyn.RET v =>
       let
         val (v', vty) = elabValue env v
       in
         (ISyn.RET v', Ty.UP vty)
       end

     | ESyn.FORCE v =>
       let
         val (v', vty) = elabValue env v
       in
         case vty of
            Ty.DOWN cty => (ISyn.FORCE v', cty)
          | _ => Err.raiseError @@ Err.GENERIC [Fpp.text "Expected down-shifted type"]
       end

     | ESyn.FN (x, vty, cmd) =>
       let
         val env' = R.extendId env x vty
         val (cmd', cty) = elabCmd env' cmd
       in
         (ISyn.FN (x, vty, cmd'), Ty.FUN (vty, cty))
       end

     | ESyn.AP (cmd, v) =>
       let
         val (cmd', cty) = elabCmd env cmd
       in
         case cty of
            Ty.FUN (vty, cty') =>
            let
              val (v', vty') = elabValue env v
            in
              if vty = vty' then 
                (ISyn.AP (cmd', v'), cty')
              else
                Err.raiseError @@ Err.GENERIC [Fpp.text "Argument type mismatch"]
            end
          | _ => Err.raiseError @@ Err.GENERIC [Fpp.text "Expected function type"]
       end

     | ESyn.PRINT (pos, v) =>
       (ISyn.PRINT (pos, #1 @@ elabValue env v), Ty.UP Ty.ONE)

     | ESyn.REFINE (ajdg, script) =>
       let
         val ajdg' = elabAtomicJdg env ajdg
         val script' = elabAst env script
       in
         (ISyn.REFINE (ajdg', script'), Ty.UP o Ty.THM @@ AJ.synthesis ajdg')
       end

     | ESyn.FRESH vls =>
       (ISyn.FRESH vls, Ty.UP @@ Ty.METAS @@ List.map #2 vls)

     | ESyn.MATCH_METAS (v, Xs, cmd) =>
       let
         val (v', Ty.METAS vls) = elabValue env v
         val (psi, env') = R.extendMetas env (Xs, vls)
         val (cmd', cty) = elabCmd env' cmd
       in
         (ISyn.MATCH_METAS (v', List.map #1 psi, cmd'), cty)
       end

     | ESyn.MATCH_THM (v, xjdg, xtm, cmd) =>
       let
         val (v', ty) = elabValue env v
         val tau =
           case ty of
              Ty.THM tau => tau
            | _ => Err.raiseError @@ Err.GENERIC [Fpp.text "MATCH_THM applied to non-theorem"]

         val env' = R.extendId env xjdg @@ Ty.TERM RedPrlSort.JDG
         val env'' = R.extendId env' xtm @@ Ty.TERM tau
         val (cmd', cty) = elabCmd env'' cmd
       in
         (ISyn.MATCH_THM (v', xjdg, xtm, cmd'), cty)
       end

     | ESyn.MATCH_ABS (v, xpsi, xv, cmd) =>
       let
         val (v', Ty.ABS (vls, vty)) = elabValue env v
         val env' = R.extendId env xpsi @@ Ty.METAS vls
         val env'' = R.extendId env' xv vty
         val (cmd', cty) = elabCmd env'' cmd
       in
         (ISyn.MATCH_ABS (v', xpsi, xv, cmd'), cty)
       end

     | ESyn.ABORT =>
       (ISyn.ABORT, Ty.UP Ty.ONE)
       (* ? *)

end
