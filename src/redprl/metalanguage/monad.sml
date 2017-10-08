structure MetalanguageMonad2 :> METALANGUAGE_MONAD2 = 
struct
  open Lcf infix |>

  type name = RedPrlAbt.variable
  type names = int -> name

  type 'a consumer = {value: 'a, consumedNames: int}

  fun consumer (a : 'a) : 'a consumer =
    {value = a, consumedNames = 0}

  fun commuteConsumer (st : 'a consumer state) : 'a state consumer =
    let
      val psi |> vld = st
      val (psi', max) = Tl.foldl (fn (x, cjdg, (psi, n)) => (Tl.snoc psi x (#value cjdg), Int.max (#consumedNames cjdg, n))) (Tl.empty, 0) psi
    in
      {value = psi' |> vld, consumedNames = max}
    end

  structure G =
  struct
    type 'a m = names * jdg state -> 'a * jdg consumer state

    fun return (a : 'a) : 'a m = fn (alpha, state) => 
      (a, Lcf.map consumer state)

    fun bind (m : 'a m) (f : 'a -> 'b m) : 'b m = fn (alpha, state) =>
      let
        val (a, state') = m (alpha, state)
        val {value = state'', consumedNames} = commuteConsumer state'
        val alpha' = UniversalSpread.bite consumedNames alpha
      in
        f a (alpha', state'')
      end

    fun seq m1 m2 = 
      bind m1 (fn _ => m2)

    fun fail _ = 
      raise Fail "Fail"
    
    fun <+> (m1, m2) (alpha, state) = 
      m1 (alpha, state) handle _ => m2 (alpha, state)
  end

  structure L =
  struct
    type 'a m = names * jdg -> ('a * jdg consumer) state

    fun isjdg' () : ('a * jdg consumer) isjdg =
      {sort = #sort isjdg o #value o #2,
       subst = fn env => fn (a, {consumedNames, value}) => (a, {consumedNames = consumedNames, value = #subst isjdg env value}),
       ren = fn ren => fn (a, {consumedNames, value}) => (a, {consumedNames = consumedNames, value = #ren isjdg ren value})}

    fun return (a : 'a) : 'a m = fn (alpha, jdg) => 
      Lcf.ret (isjdg' ()) (a, consumer jdg)

    fun bind (m : 'a m) (f : 'a -> 'b m) : 'b m = fn (alpha, jdg) => 
      let
        val state = m (alpha, jdg)
        val state' = Lcf.map (fn (a, {consumedNames, value}) => f a (UniversalSpread.bite consumedNames alpha, value)) state
      in
        Lcf.mul (isjdg' ()) state'
      end

    fun seq m1 m2 =
      bind m1 (fn _ => m2)

    fun fail _ = raise Fail "Fail"

    fun <+> (m1, m2) (alpha, jdg) =
      m1 (alpha, jdg)
      handle _ => m2 (alpha, jdg)
  end

  fun fork (ls : 'a L.m list) : 'a list G.m = fn (alpha, state : jdg state) =>
    let
      open Tl.ConsView
      fun loop (vs : 'a list, env : Lcf.L.env, acc : jdg consumer Tl.telescope) =
        fn (_, EMPTY) => (List.rev vs, env, acc)
         | (l :: ls, CONS (x, jdg, psi)) => 
           let
             val psix |> vldx = l (alpha, jdg)
             val acc' = Tl.append acc (Tl.map #2 psix)
             val env' = Lcf.L.Ctx.insert env x vldx
             val vs' = Tl.foldl (fn (_, (v, _), vs) => v :: vs) vs psix (* double check *)
           in
             loop (vs', env', acc') (ls, out psi)
           end

      val psi |> vld = state
      val (vs, env, psi') = loop ([], Lcf.L.Ctx.empty, Tl.empty) (ls, out psi)
      val vld' = Lcf.L.subst env vld
    in
      (vs, psi' |> vld')
    end

  fun enter l (alpha, state) =
    let
      val psi |> _ = state
      val ls = Tl.foldr (fn (_, _, ls) => l :: ls) [] psi
    in
      fork ls (alpha, state)
    end

  fun unfocus (m : 'a G.m) = fn (alpha, jdg) =>
    raise Match

  fun goal (alpha, jdg) =
    L.return jdg (alpha, jdg)

  fun rule tac (alpha, jdg) =
    let
      val (alpha', probe) = UniversalSpread.probe alpha
      val state = tac alpha' jdg
    in
      Lcf.map (fn jdg => ((), {consumedNames = !probe, value = jdg})) state
    end
end

structure MetalanguageMonad :> METALANGUAGE_MONAD = 
struct
  type name = RedPrlAbt.symbol
  type names = int -> name

  exception todo
  fun ?e = raise e

  open Lcf infix |>
  type 'a internal = {goal: jdg, consumedNames: int, ret: 'a}
  type 'a m = names * jdg state -> 'a internal state

  fun isjdg () : 'a internal isjdg =
    {sort = #sort Lcf.isjdg o #goal,
     subst = fn env => fn {goal, consumedNames, ret} => {goal = #subst Lcf.isjdg env goal, consumedNames = consumedNames, ret = ret},
     ren = fn ren => fn {goal, consumedNames, ret} => {goal = #ren Lcf.isjdg ren goal, consumedNames = consumedNames, ret = ret}}

  fun pure a (alpha, state) =
    Lcf.map
      (fn jdg => {goal = jdg, consumedNames = 0, ret = a})
      state

  fun maxConsumedNames (state : 'a internal state) : int =
    let
      val psi |> _ = state
    in
      Tl.foldr (fn (_, {consumedNames,...}, n) => Int.max (consumedNames, n)) 0 psi
    end

  fun bind (m : 'a m) (f : 'a -> 'b m) (alpha, state) : 'b internal state =
    let
      val state' : 'a internal state = m (alpha, state)
      val alpha' = UniversalSpread.bite (maxConsumedNames state') alpha
      val state'' = Lcf.map (fn {goal, consumedNames, ret} => f ret (alpha', Lcf.ret Lcf.isjdg goal)) state'
    in
      mul (isjdg ()) state''
    end


  fun map (f : 'a -> 'b) (m : 'a m) =
    bind m (pure o f)

  fun getGoal (alpha, state) =
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
      Lcf.mul
        (isjdg ())
        (mtac
         (Lcf.map
           (fn jdg => {consumedNames = 0, ret = (), goal = jdg})
           state))

  fun multibind (m : unit m) (ms : unit m list) (alpha, state) : unit internal state =
    let
      val state' as Lcf.|> (psi, evd) = m (alpha, state)
      val goals = Lcf.Tl.foldr (fn (x,j,r) => j::r) [] psi
      val tacs = ListPair.map (fn ({consumedNames, ...}, n) => asTactic (UniversalSpread.bite consumedNames alpha) n) (goals, ms)
    in
      fromMultitactic (LcfUtil.eachSeq tacs) (alpha, Lcf.map (fn {goal,...} => goal) state')
    end


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

  fun pushNames (names, m) (alpha, state) =
    let
      val len = List.length names
      val alpha' = UniversalSpread.prepend names alpha
      val state' = m (alpha', state)
      
      fun go {consumedNames, goal, ret} =
        {consumedNames = Int.max (0, consumedNames - len),
         goal = goal,
         ret = ret}
    in
      Lcf.map go state'
    end

  fun extract pos m (alpha, state) =
    let
      val psi |> evd = m (alpha, state)
    in
      if Tl.isEmpty psi then
        pure evd (alpha, state)
      else
        RedPrlError.raiseAnnotatedError'
          (pos, RedPrlError.GENERIC [Fpp.text "Incomplete proof"])
    end

  fun set jdg (alpha, _) : unit internal state =
    Lcf.ret (isjdg ()) {goal = jdg, consumedNames = 0, ret = ()}

  fun setState (state : jdg state) (alpha, _) : unit internal state = 
    Lcf.map (fn jdg => {consumedNames = 0, goal = jdg, ret = ()}) state

  fun >>= (m, f) = bind m f infix >>=

  fun local_ jdg m = 
    set jdg >>= (fn _ => m)

  fun print (pos, doc) (alpha, state) = 
    (RedPrlLog.print RedPrlLog.INFO (pos, doc);
     Lcf.map (fn jdg => {consumedNames = 0, goal = jdg, ret = ()}) state) 
  
  fun fail (pos, doc) (alpha, state) = 
    RedPrlError.raiseAnnotatedError' (pos, RedPrlError.GENERIC [doc])

  structure OTm = RedPrlAbt and OSyn = Syntax and CJ = RedPrlCategoricalJudgment

  fun run m =
    let
      val jdg = RedPrlSequent.>> (([], RedPrlSequentData.Hyps.empty), CJ.TERM RedPrlSortData.TRIV)
      val state : jdg state = Lcf.idn jdg
      val welp = m (fn i => RedPrlAbt.Sym.named (Int.toString i), state)
    in
      ()
    end
end
