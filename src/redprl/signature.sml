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

  structure EvalKit = 
  struct
    structure Syn = ISyn and Sem = Sem
  end


  structure Elab = MlElaborate (ElabKit)
  structure Eval = MlEvaluate (EvalKit)

  structure L = RedPrlLog

  fun checkSrcSig (sign : Src.sign) : bool =
    let
      val ecmd = compileSrcSig sign
      val (icmd, _) = Elab.elabCmd Res.init ecmd
      val (scmd, exit) = Eval.evalCmd Sem.initEnv icmd
    in
      exit
    end
end
