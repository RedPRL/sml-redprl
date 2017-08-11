signature METALANGUAGE_EVAL_KIT = 
sig
  structure ML : METALANGUAGE_SYNTAX
    where type osort = RedPrlAbt.sort
    where type oterm = RedPrlAbt.abt
    where type osym = RedPrlAbt.symbol
  structure M : METALANGUAGE_MONAD
end

functor MetalanguageEval (include METALANGUAGE_EVAL_KIT) : 
sig
  type env
  type value

  val eval : env -> ML.mlterm_ -> value M.m
end =
struct
  exception todo fun ?e = raise e

  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlCategoricalJudgment and Tm = RedPrlAbt
  structure Unify = AbtUnify (Tm)

  type mlterm = ML.mlterm_
  type scope = (ML.mlvar, mlterm) ML.scope
  type names = int -> Tm.symbol

  fun >>= (m, f) = M.bind m f infix >>=
  fun =<< (f, m) = m >>= f infixr =<<
  fun @@ (f, x) = f x infixr @@
  fun <$> (f, m) = M.map f m
  fun <&> (m1, m2) = m1 >>= (fn a1 => m2 >>= (fn a2 => M.pure (a1, a2)))
  fun flip f x y = f y x
  fun const x _ = x
  infix <&> <$>

  structure V =
  struct
    datatype value =
       NIL
     | FUN of (ML.mlvar, mlterm) ML.scope * env
     | PAIR of value * value
     | QUOTE of Tm.abt
     | THEOREM of (ML.osym, ML.oterm) CJ.jdg * Tm.abs (* a certified proof term *)

    withtype env = value ML.Ctx.dict * Tm.metaenv

    val rec ppValue = 
      fn NIL => Fpp.text "()"
       | FUN _ => Fpp.text "<fun>"
       | PAIR (v1, v2) => Fpp.Atomic.parens @@ Fpp.hsep [ppValue v1, Fpp.Atomic.comma, ppValue v2]
       | QUOTE abt => TermPrinter.ppTerm abt
       | THEOREM _ => Fpp.text "<theorem>"
  end

  structure Env =
  struct
    type env = V.env

    fun lookupMl (mlenv, _) x = ML.Ctx.lookup mlenv x
    fun insertMl (mlenv, oenv) x v = (ML.Ctx.insert mlenv x v, oenv)
    fun insertObjMeta (mlenv, oenv) x abs = (mlenv, Tm.Metavar.Ctx.insert x abs)
    fun insertObjMetas (mlenv, oenv) oenv' = (mlenv, Tm.Metavar.Ctx.union oenv oenv' (fn (_,_,abs) => abs))
    
    fun forceObjTerm (_, oenv) = Tm.substMetaenv oenv
  end

  type env = V.env
  type value = V.value

  fun fst (V.PAIR (v1, _)) = v1
  fun snd (V.PAIR (_, v2)) = v2
  fun getGoal (J.>> (_, jdg)) = V.QUOTE @@ CJ.toAbt jdg

  fun eval env (ML.:@ (term, pos) : mlterm) : V.value M.m =
    case term of
       ML.VAR x => M.pure @@ Env.lookupMl env x
     | ML.LET (t, sc) =>
       let
         val (x, tx) = ML.unscope sc
       in
         eval env t >>= 
           flip eval tx o Env.insertMl env x
       end
     | ML.NIL => M.pure V.NIL
     | ML.FUN sc => M.pure @@ V.FUN (sc, env)
     | ML.APP (t1, t2) => app =<< (eval env t1 <&> eval env t2)
     | ML.PAIR (t1, t2) => V.PAIR <$> (eval env t1 <&> eval env t2)
     | ML.FST t => fst <$> eval env t
     | ML.SND t => snd <$> eval env t
     | ML.QUOTE abt => M.pure o V.QUOTE @@ Env.forceObjTerm env abt
     | ML.GOAL => getGoal <$> M.getGoal
     | ML.REFINE ruleName => const V.NIL <$> M.rule (Rules.lookupRule ruleName)
     | ML.EACH ts => const V.NIL <$> M.fork (List.map (M.map (const ()) o eval env) ts)
     | ML.TRY (t1, t2) => M.orelse_ (eval env t1, eval env t2)
     | ML.PUSH sc =>
       let
         val (xs, t) = ML.unscope sc
       in
         M.pushNames (xs, eval env t)
       end
     | ML.PROVE (abt, t) =>
       let
         val catjdg = CJ.fromAbt @@ Env.forceObjTerm env abt
         val jdg = J.>> (([], J.Hyps.empty), catjdg)
         fun makeTheorem evd = V.THEOREM (catjdg, evd)
       in
         makeTheorem <$> M.extract (M.local_ jdg (const () <$> eval env t))
       end
     | ML.OMATCH (scrutinee, clauses) => 
       let
         fun matchWithClause abt clause =
           let
             val (metas, (pat, t)) = ML.unscope clause
             val pvars = List.foldl (fn ((x, _), metas) => Unify.Metas.insert metas x) Unify.Metas.empty metas
             val rho = Unify.unify pvars (abt, Env.forceObjTerm env pat)
           in
             eval (Env.insertObjMetas env rho) t
           end

         fun matchWithClauses abt =
           fn [] => M.fail (pos, Fpp.hsep [Fpp.text "Scrutinee", TermPrinter.ppTerm abt, Fpp.text "did not match any provided patterns"])
            | cl::cls => 
              (matchWithClause abt cl
               handle Unify.Unify _ => matchWithClauses abt cls)
       in
         eval env scrutinee >>= (fn V.QUOTE abt => matchWithClauses abt clauses)
       end
     | ML.PRINT t => 
       eval env t >>= (fn v => 
         const V.NIL <$> M.print (pos, V.ppValue v))

  and app (V.FUN (sc, env), v) =
    let
      val (x, tx) = ML.unscope sc
      val env' = Env.insertMl env x v
    in
      eval env' tx
    end
end