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

  type mlterm = ML.mlterm_
  type scope = (ML.mlvar, mlterm) ML.scope
  type names = int -> Tm.symbol

  fun >>= (m, f) = M.bind m f infixr >>=
  fun =<< (f, m) = m >>= f infix =<<
  fun @@ (f, x) = f x infixr @@
  fun <$> (f, m) = M.map f m
  fun <&> (m1, m2) = m1 >>= (fn a1 => m2 >>= (fn a2 => M.pure (a1, a2)))
  fun flip f x y = f y x
  fun const x _ = x
  infix <&> <$>

  structure Env = ML.Ctx

  structure V =
  struct
    datatype value =
       NIL
     | FUN of (ML.mlvar, mlterm) ML.scope * env
     | PAIR of value * value
     | QUOTE of Tm.abt

    withtype env = value Env.dict
  end

  type env = V.env
  type value = V.value

  fun fst (V.PAIR (v1, _)) = v1
  fun snd (V.PAIR (_, v2)) = v2
  fun getGoal (J.>> (_, jdg)) = V.QUOTE @@ CJ.toAbt jdg

  fun eval env : mlterm -> V.value M.m =
    fn ML.VAR x => M.pure @@ Env.lookup env x
     | ML.LET (t, sc) =>
       let
         val (x, tx) = ML.unscope sc
       in
         eval env t >>= 
           flip eval tx o Env.insert env x
       end
     | ML.NIL => M.pure V.NIL
     | ML.LAM sc => M.pure @@ V.FUN (sc, env)
     | ML.APP (t1, t2) => app =<< (eval env t1 <&> eval env t2)
     | ML.PAIR (t1, t2) => V.PAIR <$> (eval env t1 <&> eval env t2)
     | ML.FST t => fst <$> eval env t
     | ML.SND t => snd <$> eval env t
     | ML.QUOTE abt => M.pure @@ V.QUOTE abt
     | ML.GOAL => getGoal <$> M.get
     | ML.REFINE ruleName => const V.NIL <$> M.rule (Rules.lookupRule ruleName)
     | ML.EACH ts => const V.NIL <$> M.fork (List.map (M.map (const ()) o eval env) ts)
     | ML.TRY (t1, t2) => M.orelse_ (eval env t1, eval env t2)
     | ML.PUSH sc =>
       let
         val (xs, t) = ML.unscope sc
       in
         M.pushNames (xs, eval env t)
       end

  and app (V.FUN (sc, env), v) =
    let
      val (x, tx) = ML.unscope sc
      val env' = Env.insert env x v
    in
      eval env' tx
    end
end