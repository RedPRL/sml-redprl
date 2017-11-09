signature METALANGUAGE_EVAL_KIT = 
sig
  structure ML : METALANGUAGE_SYNTAX
    where type oterm = RedPrlAbt.abt
    where type osym = RedPrlAbt.variable
  structure M : METALANGUAGE_MONAD
end

functor MetalanguageEval (include METALANGUAGE_EVAL_KIT) : 
sig
  type env
  type value

  val eval : env -> ML.mlterm_ -> value M.m
  val eval0 : ML.mlterm_ -> value M.m
end =
struct
  exception todo fun ?e = raise e

  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlAtomicJudgment and Tm = RedPrlAbt
  structure Unify = AbtUnify (Tm)

  type mlterm = ML.mlterm_
  type scope = (ML.mlvar, mlterm) ML.scope
  type names = int -> Tm.variable

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
     | FST | SND
     | PAIR of value * value
     | QUOTE of Tm.abt
     | THEOREM of CJ.jdg * Tm.abs (* a certified proof term *)

    withtype env = value ML.Ctx.dict * Tm.metaenv

    val rec ppValue = 
      fn NIL => Fpp.text "()"
       | FUN _ => Fpp.text "<fun>"
       | PAIR (v1, v2) => Fpp.Atomic.parens @@ Fpp.hsep [ppValue v1, Fpp.Atomic.comma, ppValue v2]
       | QUOTE abt => TermPrinter.ppTerm abt
       | THEOREM (jdg, evd) => Fpp.hsepTight [Fpp.text "<", Fpp.text "theorem", RedPrlAtomicJudgment.pretty jdg, Fpp.text "ext", TermPrinter.ppAbs evd, Fpp.text ">"]
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
  structure Hyps = RedPrlSequentData.Hyps

  fun fst (V.PAIR (v1, _)) = v1
  fun snd (V.PAIR (_, v2)) = v2
  fun getGoal (J.>> (_, jdg)) = V.QUOTE @@ CJ.into jdg

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
     | ML.SEQ_FORK (t, ts) => 
       const V.NIL <$> M.multibind (const () <$> eval env t) (List.map (fn t' => const () <$> eval env t') ts)
     | ML.NIL => M.pure V.NIL
     | ML.FUN sc => M.pure @@ V.FUN (sc, env)
     | ML.APP (t1, t2) => app pos =<< (eval env t1 <&> eval env t2)
     | ML.PAIR (t1, t2) => V.PAIR <$> (eval env t1 <&> eval env t2)
     | ML.FST => M.pure V.FST
     | ML.SND => M.pure V.SND
     | ML.QUOTE abt => M.pure o V.QUOTE @@ Env.forceObjTerm env abt
     | ML.GOAL => getGoal <$> M.getGoal
     | ML.REFINE ruleName => const V.NIL <$> M.rule (Rules.lookupRule ruleName)
     | ML.TRY (t1, t2) => M.orelse_ (eval env t1, eval env t2)
     | ML.PUSH sc =>
       let
         val (xs, t) = ML.unscope sc
       in
         M.pushNames (List.map #1 xs, eval env t)
       end
     | ML.PROVE (t1, t2) =>
        eval env t1 >>= (fn V.QUOTE abt => 
          let
            val catjdg : CJ.jdg = CJ.out abt handle _ => CJ.TRUE (abt, NONE, RedPrlKind.top)
            val jdg = J.>> (Hyps.empty, catjdg)
            fun makeTheorem evd = V.THEOREM (catjdg, evd) 
          in
            makeTheorem <$>  M.extract pos (M.local_ jdg (const () <$> eval env t2))
          end)
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
     | ML.EXACT t => 
       eval env t >>= (fn V.QUOTE abt => 
         const V.NIL <$> M.rule (Rules.Exact abt))
     | ML.PRINT t => 
       eval env t >>= (fn v => 
         const V.NIL <$> M.print (pos, V.ppValue v))

  and app pos (vf, v) =
    case vf of 
       V.FUN (sc, env) => 
       let
         val (x, tx) = ML.unscope sc
         val env' = Env.insertMl env x v
       in
         eval env' tx
       end
     | V.FST => M.pure @@ fst v
     | V.SND => M.pure @@ snd v
     | _ => RedPrlError.raiseAnnotatedError' (pos, RedPrlError.GENERIC [Fpp.text "Impossible application"])

  val eval0 = eval (ML.Ctx.empty, Tm.Metavar.Ctx.empty)
end