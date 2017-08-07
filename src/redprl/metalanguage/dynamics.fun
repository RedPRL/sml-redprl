functor MetalanguageEval (ML : METALANGUAGE) =
struct
  exception todo fun ?e = raise e

  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlCategoricalJudgment

  type mlterm = ML.mlterm_
  type mlscope = (ML.mlvar, mlterm) ML.mlscope
  type names = int -> Tm.symbol

  structure M :> sig
    type 'a m
    val pure : 'a -> 'a m
    val bind : 'a m -> ('a -> 'b m) -> 'b m
    val map : ('a -> 'b) -> 'a m -> 'b m
    val get : Lcf.jdg m 
    val rule : (names -> Lcf.jdg Lcf.tactic) -> unit m
    val fork : unit m list -> unit m
    val orelse_ : 'a m * 'a m -> 'a m
  end =
  struct
    open Lcf infix |>
    type 'a internal = {goal: jdg, consumedNames: int, ret: 'a}
    type 'a m = names * jdg state -> 'a internal state

    fun isjdg () : 'a internal isjdg =
      {sort = #sort Lcf.isjdg o #goal,
       subst = fn env => fn {goal, consumedNames, ret} => {goal = #subst Lcf.isjdg env goal, consumedNames = consumedNames, ret = ret},
       ren = fn ren => fn {goal, consumedNames, ret} => {goal = #ren Lcf.isjdg ren goal, consumedNames = consumedNames, ret = ret}}

    fun pure a (alpha, state)=
      Lcf.map
        (fn jdg => {goal = jdg, consumedNames = 0, ret = a})
        state

    fun maxconsumedNames (state : 'a internal state) : int =
      let
        val psi |> _ = state
      in
        Tl.foldr (fn (_, {consumedNames,...}, n) => Int.max (consumedNames, n)) 0 psi
      end

    fun bind (m : 'a m) (f : 'a -> 'b m) (alpha, state) : 'b internal state =
      let
        val state' : 'a internal state = m (alpha, state)
        val alpha' = UniversalSpread.bite (maxconsumedNames state') alpha
        val state'' = Lcf.map (fn {goal, consumedNames, ret} => f ret (alpha', Lcf.ret Lcf.isjdg goal)) state'
      in
        mul (isjdg ()) state''
      end

    fun map (f : 'a -> 'b) (m : 'a m) =
      bind m (pure o f)

    fun get (alpha, state) =
      Lcf.map
        (fn jdg => {goal = jdg, consumedNames = 0, ret = jdg})
        state

    structure J : LCF_JUDGMENT = 
    struct
      type jdg = unit internal
      type sort = J.sort
      type env = J.env
      type ren = J.ren

      val isjdg : jdg isjdg = isjdg ()
      val {sort, subst, ren} = isjdg
      fun eq (jdg1 : jdg, jdg2 : jdg) = J.eq (#goal jdg1, #goal jdg2)
    end

    structure LcfUtil = LcfUtil (structure Lcf = Lcf and J = J)


    fun asTactic alpha (m : unit m) : J.jdg tactic = fn {goal, ...} => 
      m (alpha, idn goal)

    fun fromMultitactic (mtac : J.jdg multitactic) : unit m =
      fn (alpha, state) =>
        Lcf.mul (isjdg ()) (mtac (pure () (alpha, state)))

    fun fork (ms : unit m list) : unit m =
      fn (alpha, state) =>
        fromMultitactic
          (LcfUtil.eachSeq (List.map (asTactic alpha) ms))
          (alpha, state)

    fun liftTactic (tac : names -> Lcf.jdg tactic) (alpha : names) : J.jdg tactic = 
      fn {goal, consumedNames, ret} =>
        let
          val (alpha', probe) = UniversalSpread.probe alpha
          val state = tac alpha' goal
        in
          Lcf.map
            (fn jdg => {goal = jdg, consumedNames = consumedNames + !probe, ret = ret})
            state
        end

    fun rule (tac : names -> Lcf.jdg Lcf.tactic) (alpha, state) = 
      let
        val state' = Lcf.map (fn jdg => {consumedNames = 0, goal = jdg, ret = ()}) state
      in
        Lcf.mul (isjdg ()) (LcfUtil.allSeq (liftTactic tac alpha) state')
      end

    fun orelse_ (m1, m2) (alpha, state) =
      m1 (alpha, state)
        handle _ => 
          m2 (alpha, state)
  end

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