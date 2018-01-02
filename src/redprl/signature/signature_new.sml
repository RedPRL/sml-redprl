structure SignatureNew : SIGNATURE_NEW = 
struct
  structure EM = ElabMonad
  type 'a m = 'a EM.t

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
       TERM of arity
     | ONE
     | DOWN of cty
    and cty = 
       UP of vty
     | THM of arity
  end

  structure Res :>
  sig
    type env

    val lookupId : env -> string -> Ty.vty m
    val extendId : env -> string -> Ty.vty -> env m

    val lookupVar : env -> string -> (Tm.variable * Tm.sort) m
    val lookupMeta : env -> string -> (Tm.metavariable * Tm.valence) m

    val extendVars : env -> string list * Tm.sort list -> (Tm.variable list * env) m
  end = 
  struct
    type env =
      {ids : Ty.vty StringListDict.dict}
      
    fun lookupId (env : env) nm =
      case StringListDict.find (#ids env) nm of
         SOME nm' => EM.ret nm'
       | NONE => EM.fail (NONE, Fpp.hsep [Fpp.text "Could not resolve name", Fpp.text nm])

    (* TODO: ensure that this name is not already used *)
    fun extendId {ids} nm vty =
      EM.ret {ids = StringListDict.insert ids nm vty}

    fun lookupVar _ = ?todo
    fun extendVars _ = ?todo
    fun lookupMeta _ = ?todo
  end

  structure ESyn =
  struct
    datatype value = 
       THUNK of cmd
     | VAR of string
     | NIL

    and cmd = 
       BIND of cmd * string * cmd
     | RET of value
     | FORCE of value
     | PRINT of value
     | REFINE of ast * ast
  end

  structure ISyn =
  struct
    datatype value = 
       THUNK of cmd
     | VAR of string
     | NIL

    and cmd = 
       BIND of cmd * string * cmd
     | RET of value
     | FORCE of value
     | PRINT of value
     | REFINE of ajdg * abt
  end

  structure Sem = 
  struct
    datatype value = 
       THUNK of env * ISyn.cmd
     | STATE of Lcf.jdg * Lcf.jdg Lcf.state
     | NIL

    withtype env = value StringListDict.dict

    datatype cmd = RET of value

    fun lookup (env : env) (nm : string) : value m =
      case StringListDict.find env nm of 
         SOME v => EM.ret v
       | NONE => EM.fail (NONE, Fpp.hsep [Fpp.text "Could not find value of", Fpp.text nm, Fpp.text "in environment"])

    fun extend (env : env) (nm : string) (v : value) : env =
      StringListDict.insert env nm v

    val ppValue : value -> Fpp.doc = 
      fn THUNK _ => Fpp.text "<thunk>"
       | STATE _ => Fpp.text "<lcf-state>"
       | NIL => Fpp.text "()"

    fun printVal (v : value) : unit m =
      EM.info (NONE, ppValue v)
  end


  fun @@ (f, x) = f x
  infixr @@

  fun >>= (m, k) = EM.bind k m
  infix >>=

  fun zipWithM (k : 'a * 'b -> 'c m) : 'a list * 'b list -> 'c list m =
    fn ([], []) =>
       EM.ret []
     
     | (x :: xs, y :: ys) =>
       k (x, y) >>= (fn z =>
         zipWithM k (xs, ys) >>= (fn zs =>
           EM.ret @@ z :: zs))

     | _ =>
       EM.fail (NONE, Fpp.text "zipWithM: length mismatch")

  fun inferVal (renv : Res.env) : ISyn.value -> Ty.vty m =
    fn ISyn.THUNK cmd =>
       inferCmd renv cmd >>= (fn cty =>
         EM.ret @@ Ty.DOWN cty)

     | ISyn.VAR nm =>
       Res.lookupId renv nm >>= (fn vty =>
         EM.ret vty)

     | ISyn.NIL =>
       EM.ret Ty.ONE

  and inferCmd (renv : Res.env) : ISyn.cmd -> Ty.cty m =
    fn ISyn.BIND (cmd1, nm, cmd2) =>
       inferCmdAsThunk renv cmd1 >>= (fn vty1 =>
         Res.extendId renv nm vty1 >>= (fn env' =>
           inferCmd env' cmd2))

     | ISyn.RET v =>
       inferVal renv v >>= (fn vty => 
         EM.ret @@ Ty.UP vty)

     | ISyn.PRINT _ =>
       EM.ret @@ Ty.UP Ty.ONE

     | ISyn.REFINE _ => ?todo

  and inferCmdAsThunk (renv : Res.env) (cmd : ISyn.cmd) : Ty.vty m =
    inferCmd renv cmd >>= (fn cty =>
      case cty of
         Ty.UP vty => EM.ret vty
       | _ => EM.fail (NONE, Fpp.text "Expected thunked value type"))  
  
  local
    structure O = RedPrlOperator and S = RedPrlSort
  in
    fun lookupArity (renv : Res.env) (opid : string) : arity m =
      Res.lookupId renv opid >>= (fn vty =>
        case vty of 
           Ty.TERM ar => EM.ret @@ ar
         | Ty.DOWN (Ty.THM ar) => EM.ret @@ ar
         | _ => EM.fail (NONE, Fpp.hsep [Fpp.text "Could not infer arity for opid", Fpp.text opid]))

    fun checkAbt (view, tau) : abt m = 
      EM.ret @@ Tm.check (view, tau)
      handle exn => 
        EM.fail (NONE, Fpp.hsep [Fpp.text "Error resolving abt:", Fpp.text (exnMessage exn)])

    fun guessSort (renv : Res.env) (ast : ast) : sort m =
      case Ast.out ast of 
         Ast.` x =>
         Res.lookupVar renv x >>= (fn (_, tau) =>
           EM.ret tau)

       | Ast.$# (X, _) =>
         Res.lookupMeta renv X >>= (fn (_, (_, tau)) =>
           EM.ret tau)

       | Ast.$ (O.CUST (opid, _), _) =>
         lookupArity renv opid >>= (fn (_, tau) =>
           EM.ret tau)

       | Ast.$ (theta, _) =>
         (EM.ret @@ #2 (O.arity theta)
          handle _ => EM.fail (NONE, Fpp.text "Error guessing sort"))

    fun resolveAjdg (renv : Res.env) (ast : ast) : ajdg m =
      resolveAst renv (ast, S.JDG) >>= (fn abt =>
        EM.ret @@ AJ.out abt
        handle _ =>
          EM.fail (NONE, Fpp.hsep [Fpp.text "Expected atomic judgment but got", TermPrinter.ppTerm abt]))

    and resolveAst (renv : Res.env) (ast : ast, tau : sort) : abt m =
      case Ast.out ast of 
         Ast.` x =>
         Res.lookupVar renv x >>= (fn (x', _) => 
           checkAbt (Tm.` x', tau))

       | Ast.$# (X, asts : ast list) =>
         Res.lookupMeta renv X >>= (fn (X', (taus : sort list, _)) => 
           zipWithM (resolveAst renv) (asts, taus) >>= (fn abts => 
             checkAbt (Tm.$# (X', abts), tau)))

       | Ast.$ (theta, bs) =>
         resolveOpr renv theta bs >>= (fn theta' =>
           let
             val (vls, tau) = O.arity theta'
           in
             zipWithM (resolveBnd renv) (vls, bs) >>= (fn bs' =>
               checkAbt (Tm.$ (theta', bs'), tau))
           end)

    and resolveBnd (renv : Res.env) ((taus, tau), Ast.\ (xs, ast)) : abt Tm.bview m =
      Res.extendVars renv (xs, taus) >>= (fn (xs', renv') =>
        resolveAst renv' (ast, tau) >>= (fn abt =>
          EM.ret @@ Tm.\ (xs', abt)))

    and resolveOpr (renv : Res.env) (theta : O.operator) (bs : ast Ast.abs list) : O.operator m = 
      (case theta of 
         O.CUST (opid, NONE) =>
         lookupArity renv opid >>= (fn ar =>
           EM.ret @@ O.CUST (opid, SOME ar))

       | O.DEV_APPLY_LEMMA (opid, NONE, pat) => 
         lookupArity renv opid >>= (fn ar =>
           EM.ret @@ O.DEV_APPLY_LEMMA (opid, SOME ar, pat))

       | O.DEV_USE_LEMMA (opid, NONE) =>
         lookupArity renv opid >>= (fn ar =>
           EM.ret @@ O.DEV_USE_LEMMA (opid, SOME ar))

       | O.MK_ANY NONE =>
         let
           val [Ast.\ (_, ast)] = bs
         in
           guessSort renv ast >>= (fn tau =>
             EM.ret @@ O.MK_ANY (SOME tau))
         end

       | O.DEV_LET NONE =>
         let
           val [Ast.\ (_, jdg), _, _] = bs
         in
           resolveAjdg renv jdg >>= (fn ajdg =>
             EM.ret @@ O.DEV_LET @@ SOME @@ AJ.synthesis ajdg)
         end

       | th => EM.ret th)
       handle _ => 
         EM.fail (NONE, Fpp.text "Error resolving operator")
  end

  fun resolveVal (renv : Res.env) : ESyn.value -> ISyn.value m = 
    fn ESyn.THUNK cmd =>
       resolveCmd renv cmd >>= (fn cmd' => 
         EM.ret @@ ISyn.THUNK cmd')
     | ESyn.VAR nm => EM.ret @@ ISyn.VAR nm

  and resolveCmd (renv : Res.env) : ESyn.cmd -> ISyn.cmd m = 
    fn ESyn.BIND (cmd1, nm, cmd2) =>
       resolveCmd renv cmd1 >>= (fn cmd1' =>
         inferCmdAsThunk renv cmd1' >>= (fn vty =>
           Res.extendId renv nm vty >>= (fn renv' =>
             resolveCmd renv' cmd2 >>= (fn cmd2' => 
               EM.ret @@ ISyn.BIND (cmd1', nm, cmd2')))))

     | ESyn.RET v =>
       resolveVal renv v >>= (fn v' =>
         EM.ret @@ ISyn.RET v')

     | ESyn.FORCE v =>
       resolveVal renv v >>= (fn v' =>
         EM.ret @@ ISyn.FORCE v')

     | ESyn.PRINT v =>
       resolveVal renv v >>= (fn v' => 
         EM.ret @@ ISyn.PRINT v')

     | ESyn.REFINE (ajdg, script) =>
       resolveAjdg renv ajdg >>= (fn ajdg' => 
         resolveAst renv (script, RedPrlSort.TAC) >>= (fn script' => 
           EM.ret @@ ISyn.REFINE (ajdg', script')))


  fun evalCmd (env : Sem.env) : ISyn.cmd -> Sem.cmd m =
    fn ISyn.BIND (cmd1, x, cmd2) =>
       evalCmd env cmd1 >>= (fn Sem.RET s =>
         evalCmd (Sem.extend env x s) cmd2)

     | ISyn.RET v => 
       evalVal env v >>= (fn s =>
         EM.ret @@ Sem.RET s)

     | ISyn.FORCE v => 
       evalVal env v >>= (fn s =>
         case s of 
            Sem.THUNK (env', cmd) => evalCmd env' cmd
          | _ => EM.fail (NONE, Fpp.text "evalCmd/ISyn.FORCE expected Sem.THUNK"))

     | ISyn.PRINT v =>
       evalVal env v >>= (fn s => 
         Sem.printVal s >>= (fn _ => 
           EM.ret @@ Sem.RET @@ Sem.NIL))

     | ISyn.REFINE (ajdg, script) =>
       ?todo

  and evalVal (env : Sem.env) : ISyn.value -> Sem.value m =
    fn ISyn.THUNK cmd => 
       EM.ret @@ Sem.THUNK (env, cmd)

     | ISyn.VAR nm =>
       Sem.lookup env nm

     | ISyn.NIL =>
       EM.ret Sem.NIL
end