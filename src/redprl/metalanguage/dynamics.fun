functor MetalanguageEval (ML : METALANGUAGE) =
struct
  exception todo fun ?e = raise e

  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlCategoricalJudgment

  type mlterm = ML.mlterm_
  type mlscope = (ML.mlvar, mlterm) ML.mlscope
  type names = int -> Tm.symbol

  structure F : sig
    type 'a m
    val pure : 'a -> 'a m
    val bind : 'a m * ('a -> 'b m) -> 'b m
    val get : Lcf.jdg m
    val rule : 'a -> (names -> Lcf.jdg Lcf.tactic) -> 'a m
  end =
  struct
    type 'a m = names * Lcf.jdg -> int * (Lcf.jdg * 'a) Lcf.state
    fun isjdg () : (Lcf.jdg * 'a) Lcf.isjdg =
      {sort = #sort Lcf.isjdg o #1,
       subst = fn env => fn (j, n) => (#subst Lcf.isjdg env j, n),
       ren = fn ren => fn (j, n) => (#ren Lcf.isjdg ren j, n)}

    fun pure a (alpha, jdg) = (0, Lcf.ret (isjdg ()) (jdg, a))
    fun bind (m : 'a m, f : 'a -> 'b m) (alpha, jdg) =
      let
        val (n, state') = m (alpha, jdg)
        val alpha' = UniversalSpread.bite n alpha
        val Lcf.|> (psi, vld)  = Lcf.map (fn (jdg, a) => f a (alpha', jdg)) state'
        val n = Lcf.Tl.foldr (fn (_,(n',_),n) => Int.max (n', n)) 0 psi
        val psi' = Lcf.Tl.map (fn (n, j) => j) psi
        val welp = Lcf.mul (isjdg ()) (Lcf.|> (psi', vld))
      in
        (n, welp)
      end

    fun get (alpha, jdg) = (0, Lcf.ret (isjdg ()) (jdg, jdg))
    fun rule a tac (alpha, jdg) = 
      let
        val (alpha', probe) = UniversalSpread.probe alpha
        val state = tac alpha' jdg
      in
        (!probe, Lcf.map (fn j => (j, a)) state)
      end
  end

  val >>= = F.bind infixr >>=
  fun =<< (f, m) = m >>= f infix =<<
  fun @@ (f, x) = f x infixr @@
  fun <$> (f, m) = m >>= (fn a => F.pure (f a))
  fun <&> (m1, m2) = m1 >>= (fn a1 => m2 >>= (fn a2 => F.pure (a1, a2)))
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

  fun tactic env : mlterm -> V.value F.m =
    fn ML.VAR x => F.pure @@ Env.lookup env x
     | ML.LET (t, sc) =>
       let
         val (x, tx) = ML.unscope sc
       in
         tactic env t >>= (fn v => 
           tactic (Env.insert env x v) tx)
       end
     | ML.LAM sc => F.pure @@ V.FUN (sc, env)

     | ML.APP (t1, t2) => app =<< (tactic env t1 <&> tactic env t2)
     | ML.PAIR (t1, t2) => V.PAIR <$> (tactic env t1 <&> tactic env t2)
     | ML.FST t => fst <$> tactic env t
     | ML.SND t => snd <$> tactic env t
     | ML.QUOTE m => F.pure @@ V.QUOTE m
     | ML.GOAL => getGoal <$> F.get
     | ML.REFINE ruleName => F.rule V.NIL @@ Rules.lookupRule ruleName

  and app (V.FUN (sc, env), v) =
    let
      val (x, tx) = ML.unscope sc
      val env' = Env.insert env x v
    in
      tactic env' tx
    end

end


functor MetalanguageDynamics (ML : METALANGUAGE) =
struct
  datatype hole = HOLE
  datatype ('a, 'b) closure = <: of 'a * ('b, 'b) closure ML.Ctx.dict

  structure Rules = Refiner (Signature)
  structure J = RedPrlSequent and CJ = RedPrlCategoricalJudgment

  type mlterm = ML.mlterm_
  type mlscope = (ML.mlvar, mlterm) ML.mlscope

  datatype continuation =
     FUN of hole * mlterm
   | ARG of mlscope * hole
   | LET of ML.mlvar * hole * mlterm
   | PAIR0 of hole * mlterm
   | PAIR1 of mlterm * hole
   | FST of hole
   | SND of hole
   | EACH of {tactics: mlterm list, done: Lcf.jdg Lcf.Tl.telescope, metaenv: Tm.metaenv}
   | SPLICE of {tactics: mlterm list, var: Lcf.L.var, done: Lcf.jdg Lcf.Tl.telescope, remaining: Lcf.jdg Lcf.Tl.telescope, metaenv: Tm.metaenv}

  type stack = (continuation, mlterm) closure list

  type names = int -> Tm.symbol
  datatype state = LOCAL of Lcf.jdg | GLOBAL of Lcf.jdg Lcf.state
  datatype control = ## of (state * names) * (mlterm, mlterm) closure
  datatype machine = |> of control * stack | <| of control * stack

  infix 3 ##
  infix 6 <:
  infix 2 <| |>

  exception todo fun ?e = raise e

  structure Tactical = RedPrlTactical (Lcf)

  fun applyRule (rule : Rules.rule) (jdg, alpha) : state * names =
    let
      val (alpha', probe) = UniversalSpread.probe alpha
      val state' = rule alpha' jdg
      val beta = UniversalSpread.bite (!probe) alpha
    in
      (GLOBAL state', beta)
    end

  exception Final
  exception Stuck

  val step =
    fn _ ## _ <: _ |> [] => raise Final
     | st ## ML.VAR x <: env <| ks => st ## ML.Ctx.lookup env x |> ks
     | st ## ML.LET (t, sc) <: env <| ks =>
       let
         val (x, tx) = ML.unscope sc
       in
         st ## t <: env <| LET (x, HOLE, tx) <: env :: ks
       end
     | st ## v <: env |> LET (x, HOLE, tx) <: env' :: ks => st ## tx <: ML.Ctx.insert env' x (v <: env) <| ks
     | st ## ML.LAM sc <: env <| ks => st ## ML.LAM sc <: env |> ks
     | st ## ML.APP (t1, t2) <: env <| ks => st ## t1 <: env <| FUN (HOLE, t2) <: env :: ks
     | st ## ML.LAM sc <: env |> FUN (HOLE, t) <: env' :: ks => st ## t <: env' <| ARG (sc, HOLE) <: env :: ks
     | st ## v <: env |> ARG (sc, HOLE) <: env' :: ks =>
       let
         val (x, tx) = ML.unscope sc
       in
         st ## tx <: ML.Ctx.insert env' x (v <: env) <| ks
       end
     | st ## ML.PAIR (t1, t2) <: env <| ks => st ## t1 <: env <| PAIR0 (HOLE, t2) <: env :: ks
     | st ## v <: env |> PAIR0 (HOLE, t) <: env' :: ks => st ## t <: env' <| PAIR1 (v, HOLE) <: env :: ks
     | st ## v <: env |> PAIR1 (v', HOLE) <: env' :: ks =>
       let
         val x = ML.freshVar ()
         val y = ML.freshVar ()
         val envxy = ML.Ctx.insert (ML.Ctx.singleton x (v' <: env')) y (v <: env)
       in
         st ## ML.PAIR (ML.VAR x, ML.VAR y) <: envxy |> ks
       end
     | st ## ML.FST t <: env <| ks => st ## t <: env <| FST HOLE <: env :: ks
     | st ## ML.SND t <: env <| ks => st ## t <: env <| SND HOLE <: env :: ks
     | st ## ML.PAIR (v1, _) <: env |> FST HOLE <: _ :: ks => st ## v1 <: env |> ks
     | st ## ML.PAIR (_, v2) <: env |> SND HOLE <: _ :: ks => st ## v2 <: env |> ks
     | st ## ML.QUOTE tm <: env <| ks => st ## ML.QUOTE tm <: env |> ks
     | (st as (LOCAL (J.>> (_, goal)), _)) ## ML.GOAL <: _ <| ks =>
       st ## ML.QUOTE (CJ.toAbt goal) <: ML.Ctx.empty |> ks
     | (LOCAL jdg, alpha) ## ML.REFINE ruleName <: env <| ks =>
       let
         val rule = Rules.lookupRule ruleName
         val st' = applyRule rule (jdg, alpha)
       in
         st' ## ML.NIL <: ML.Ctx.empty |> ks
       end
     | (st as (GLOBAL state, _)) ## ML.ALL t <: env <| ks =>
       let
         val Lcf.|> (psi, _) = state
         val ts = Lcf.Tl.foldr (fn (_, _, ts) => t::ts) [] psi
         val eachState = {tactics = ts, done = Lcf.Tl.empty, metaenv = Tm.Metavar.Ctx.empty}
       in
         st ## ML.NIL <: ML.Ctx.empty |> EACH eachState <: env :: ks
       end

     | (GLOBAL state, alpha) ## _ <: _ |> EACH {tactics, done, metaenv} <: env :: ks =>
       let
         val Lcf.|> (psi, evd) = state
         open Lcf.Tl.ConsView
       in
         case (out psi, tactics) of
            (EMPTY, []) => (GLOBAL (Lcf.|> (done, evd)), alpha) ## ML.NIL <: ML.Ctx.empty |> ks
          | (CONS (x, jdg, psi), t :: ts) =>
            let
              val jdg' = Lcf.J.subst metaenv jdg
              val spliceState = {tactics = ts, var = x, done = done, remaining = psi, metaenv = metaenv}
            in
              (LOCAL jdg', alpha) ## t <: env <| SPLICE spliceState <: env :: ks
            end
       end

     | (GLOBAL state, alpha) ## _ <: _ |> SPLICE {tactics, var = x, done, remaining, metaenv} <: env :: ks =>
       let
         val Lcf.|> (psi, evd) = state
         val metaenv' = Tm.Metavar.Ctx.insert metaenv x evd
         val state' = Lcf.|> (remaining, evd)
         val eachState = {tactics = tactics, done = Lcf.Tl.append psi done, metaenv = metaenv'}
       in
         (GLOBAL state', alpha) ## ML.NIL <: ML.Ctx.empty |> EACH eachState <: env :: ks
       end

     | _ => raise Stuck

  exception todo fun ?e = raise e

  fun init (alpha, jdg) mlterm =
    (LOCAL jdg, alpha) ## mlterm <: ML.Ctx.empty <| []

  fun steps cfg =
    steps (step cfg)
    handle Final => cfg

  fun compile mlterm alpha : Lcf.jdg Lcf.tactic =
    fn jdg =>
    let
      val (GLOBAL state, _) ## _ |> _ = steps (init (alpha, jdg) mlterm)
    in
      state
    end

  local
    open ML open J infix >>
    structure CJ = RedPrlCategoricalJudgment and Syn = Syntax
    fun @@ (f, x) = f x infixr @@
  in
    val testScript =
      resolve @@
        LET (REFINE "dfun/intro", strScope ("x", VAR "x"))

    val jdg : Lcf.jdg = ([], Hyps.empty) >> CJ.TRUE (Syn.into @@ Syn.DFUN (Syn.into @@ Syn.BOOL, Tm.Var.named "_", Syn.into @@ Syn.BOOL))
    val alpha = Tm.Sym.named o Int.toString
    fun test () =
      let
        val state = compile testScript alpha jdg
      in
        FppRenderPlainText.render TextIO.stdErr (FinalPrinter.execPP (Lcf.prettyState state));
        state
      end
  end

end

structure MLDynamics = MetalanguageDynamics (Metalanguage)