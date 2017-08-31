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
