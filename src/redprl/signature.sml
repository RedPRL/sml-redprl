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
  structure ESyn = MlExtSyntax

  (* internal language *)
  structure ISyn = MlIntSyntax

  fun compileSrcCmd pos : Src.cmd -> ESyn.cmd =
    fn Src.PRINT nm =>
       ESyn.PRINT (SOME pos, ESyn.VAR nm)

     | Src.EXTRACT nm =>
       ESyn.PRINT_EXTRACT (SOME pos, ESyn.VAR nm)

     | Src.QUIT =>
       ESyn.ABORT

  fun compileSrcDecl name : Src.decl -> ESyn.cmd =
    fn Src.DEF {arguments, sort, definiens} =>
       ESyn.TERM_ABS (arguments, (definiens, sort))

     | Src.TAC {arguments, script} => 
       ESyn.TERM_ABS (arguments, (script, RedPrlSort.TAC))

     | Src.THM {arguments, goal, script} =>
       ESyn.THM_ABS (SOME name, arguments, goal, (script, RedPrlSort.TAC))

  val rec compileSrcSig : Src.sign -> ESyn.cmd =
    fn [] =>
       ESyn.RET ESyn.NIL

     | Src.CMD (c, pos) :: sign =>
       ESyn.BIND (compileSrcCmd pos c, MlId.new (), compileSrcSig sign)

     | Src.DECL (nm, decl, _) :: sign =>
       ESyn.BIND (compileSrcDecl (MlId.toString nm) decl, nm, compileSrcSig sign)
  
  
  structure EvalKit = 
  struct
    structure Syn = ISyn and Sem = MlSemantics
  end

  structure Elab = MlElaborate (structure R = Res)
  structure Eval = MlEvaluate

  structure L = RedPrlLog

  fun checkSrcSig (sign : Src.sign) : bool =
    let
      val ecmd = compileSrcSig sign
      val (icmd, _) = Elab.elabCmd Res.init ecmd
      val (scmd, exit) = Eval.evalCmd MlSemantics.initEnv icmd
    in
      exit
    end
end
