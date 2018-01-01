structure SignatureNew : SIGNATURE_NEW = 
struct
  structure EM = ElabMonad
  type 'a m = 'a EM.t

  type name = Sym.t
  type ast = RedPrlAst.ast
  type arity = RedPrlArity.t
  type abt = RedPrlAbt.abt
  type ajdg = AtomicJudgment.jdg

  exception todo
  fun ?e = raise e  

  structure Res :>
  sig
    type env

    val lookupId : env -> string -> name m
    val extendId : env -> string -> (env * name) m
  end = 
  struct
    type env =
      {ids : name StringListDict.dict}
      
    fun lookupId (env : env) nm =
      case StringListDict.find (#ids env) nm of
         SOME nm' => EM.ret nm'
       | NONE => EM.fail (NONE, Fpp.hsep [Fpp.text "Could not resolve name", Fpp.text nm])

    fun extendId {ids} nm =
      let
        val nm' = Sym.named nm
      in
        EM.ret ({ids = StringListDict.insert ids nm nm'}, nm')
      end
  end

  structure Src =
  struct
    datatype value = 
       THUNK of cmd
     | VAR of string

    and cmd = 
       BIND of cmd * string * cmd
     | RET of value
     | FORCE of value
     | PRINT of value
     | REFINE of ast * ast
  end

  structure Syn =
  struct
    datatype value = 
       THUNK of cmd
     | VAR of name
     | STATE of Lcf.jdg * Lcf.jdg Lcf.state
     | NIL

    and cmd = 
       BIND of cmd * name * cmd
     | RET of value
     | FORCE of value
     | PRINT of value
     | REFINE of ajdg * abt
  end

  structure Sem = 
  struct
    datatype value = 
       THUNK of env * Syn.cmd
     | STATE of Lcf.jdg * Lcf.jdg Lcf.state
     | NIL

    withtype env = value Sym.Ctx.dict

    datatype cmd = RET of value

    fun lookup (env : env) (nm : name) : value m =
      case Sym.Ctx.find env nm of 
         SOME v => EM.ret v
       | NONE => EM.fail (NONE, Fpp.hsep [Fpp.text "Could not find value of", Fpp.text (Sym.toString nm), Fpp.text "in environment"])

    fun extend (env : env) (nm : name) (v : value) : env =
      Sym.Ctx.insert env nm v

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

  local
    structure Ast = RedPrlAst and Abt = RedPrlAbt
  in
    fun resolveAjdg (env : Res.env) (ast : ast) : ajdg m =
      case Ast.out ast of 
         _ => ?todo

    and resolveAst (env : Res.env) (ast : ast) : abt m =
      case Ast.out ast of 
         _ => ?todo
  end

  fun resolveVal (env : Res.env) : Src.value -> Syn.value m = 
    fn Src.THUNK cmd =>
       resolveCmd env cmd >>= (fn cmd' => 
         EM.ret @@ Syn.THUNK cmd')
     | Src.VAR nm =>
       Res.lookupId env nm >>= (fn nm' => 
         EM.ret @@ Syn.VAR nm')

  and resolveCmd (env : Res.env) : Src.cmd -> Syn.cmd m = 
    fn Src.BIND (cmd1, nm, cmd2) =>
       resolveCmd env cmd1 >>= (fn cmd1' =>
         Res.extendId env nm >>= (fn (env', nm') =>
           resolveCmd env' cmd2 >>= (fn cmd2' => 
             EM.ret @@ Syn.BIND (cmd1', nm', cmd2'))))

     | Src.RET v =>
       resolveVal env v >>= (fn v' =>
         EM.ret @@ Syn.RET v')

     | Src.FORCE v =>
       resolveVal env v >>= (fn v' =>
         EM.ret @@ Syn.FORCE v')

     | Src.PRINT v =>
       resolveVal env v >>= (fn v' => 
         EM.ret @@ Syn.PRINT v')

     | Src.REFINE (ajdg, script) =>
       resolveAjdg env ajdg >>= (fn ajdg' => 
         resolveAst env script >>= (fn script' => 
           EM.ret @@ Syn.REFINE (ajdg', script')))


  fun evalCmd (env : Sem.env) : Syn.cmd -> Sem.cmd m =
    fn Syn.BIND (cmd1, x, cmd2) =>
       evalCmd env cmd1 >>= (fn Sem.RET s =>
         evalCmd (Sem.extend env x s) cmd2)

     | Syn.RET v => 
       evalVal env v >>= (fn s =>
         EM.ret @@ Sem.RET s)

     | Syn.FORCE v => 
       evalVal env v >>= (fn s =>
         case s of 
            Sem.THUNK (env', cmd) => evalCmd env' cmd
          | _ => EM.fail (NONE, Fpp.text "evalCmd/Syn.FORCE expected Sem.THUNK"))

     | Syn.PRINT v =>
       evalVal env v >>= (fn s => 
         Sem.printVal s >>= (fn _ => 
           EM.ret @@ Sem.RET @@ Sem.NIL))

     | Syn.REFINE (ajdg, script) =>
       ?todo

  and evalVal (env : Sem.env) : Syn.value -> Sem.value m =
    fn Syn.THUNK cmd => 
       EM.ret @@ Sem.THUNK (env, cmd)

     | Syn.VAR nm =>
       Sem.lookup env nm

     | Syn.STATE st => 
       EM.ret @@ Sem.STATE st

     | Syn.NIL =>
       EM.ret Sem.NIL
end