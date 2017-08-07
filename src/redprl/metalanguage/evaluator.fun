functor MetalanguageEval (structure ML : METALANGUAGE and M : METALANGUAGE_MONAD) =
struct
  exception todo fun ?e = raise e

  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlCategoricalJudgment

  type mlterm = ML.mlterm_
  type mlscope = (ML.mlvar, mlterm) ML.mlscope
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
     | FUN of (ML.mlvar, mlterm) ML.mlscope * env
     | PAIR of value * value
     | QUOTE of Tm.abt

    withtype env = value Env.dict
  end

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

  and app (V.FUN (sc, env), v) =
    let
      val (x, tx) = ML.unscope sc
      val env' = Env.insert env x v
    in
      eval env' tx
    end
end