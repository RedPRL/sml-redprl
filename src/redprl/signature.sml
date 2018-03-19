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
    type elt = MlExtSyntax.cmd -> MlExtSyntax.cmd
    type sign = elt list
  end

  (* external language *)
  structure ESyn = MlExtSyntax

  structure Elab = MlElaborate (Res)
  structure Eval = MlEvaluate

  fun checkSrcSig (sign : Src.sign) : bool =
    let
      val emp = ESyn.RET ESyn.NIL
      val ecmd = List.foldr (fn (frame, sign) => frame sign) emp sign
      val (icmd, _) = Elab.elabCmd ecmd Res.init
      val (scmd, exit) = Eval.evalCmd MlSemantics.initEnv icmd
    in
      exit
    end
end
