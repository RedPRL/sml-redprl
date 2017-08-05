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
    val bind : 'a m * ('a -> 'b m) -> 'b m
    val get : Lcf.jdg m 
    val rule : (names -> Lcf.jdg Lcf.tactic) -> unit m
    val fork : unit m list -> unit m
  end =
  struct
    open Lcf infix |>
    type 'a m = names * jdg state -> int * (jdg * 'a) state

    fun isjdg () : (jdg * 'a) isjdg =
      {sort = #sort Lcf.isjdg o #1,
       subst = fn env => fn (j, n) => (#subst Lcf.isjdg env j, n),
       ren = fn ren => fn (j, n) => (#ren Lcf.isjdg ren j, n)}

    fun pure a (alpha, state) = (0, Lcf.map (fn jdg => (jdg, a)) state)
    fun bind (m : 'a m, f : 'a -> 'b m) (alpha, state) =
      let
        val (n, state' : (jdg * 'a) Lcf.state) = m (alpha, state)
        val alpha' = UniversalSpread.bite n alpha
        val psi |> evd = Lcf.map (fn (jdg, a) => f a (alpha', Lcf.ret Lcf.isjdg jdg)) state'
        val n = Tl.foldr (fn (_, (n', _), n) => Int.max (n', n)) 0 psi
        val psi' = Tl.map (fn (n, j) => j) psi
      in
        (n, mul (isjdg ()) (psi' |> evd))
      end

    fun dup x = (x, x)
    fun get (alpha, state) = 
      (0, Lcf.map dup state)

    fun rule tac (alpha, state) = 
      let
        val (alpha', probe) = UniversalSpread.probe alpha
        val state' = Lcf.mul Lcf.isjdg (Lcf.allSeq (tac alpha') state)
      in
        (!probe, Lcf.map (fn j => (j, ())) state')
      end

    fun asTactic (m : unit m) : jdg tactic = ?todo

    fun fork ms (alpha, psi |> evd) =
      let
        open Lcf.Tl
        open ConsView
        fun go rho n (r : (jdg * unit) state telescope) =
          fn (_, EMPTY) => (n, r)
           | ((m : unit m) :: ms, CONS (x, (jdg, ()), psi)) =>
             let
               val (n':int, tjdg as psix |> vlx) = m (alpha, idn (J.subst rho jdg))
               val rho' = L.Ctx.insert rho x vlx
             in
               go rho' (Int.max (n, n')) (Tl.snoc r x tjdg) (ms, out psi)
             end
           | ([], CONS (x, jdg, psi)) => 
              go rho n (Tl.snoc r x (Lcf.ret (isjdg ()) jdg)) ([], out psi)
        val (n, ppsi) = go L.Ctx.empty 0 Tl.empty (ms, out (Tl.map (fn jdg => (jdg, ())) psi))
      in
        (n, Lcf.mul (isjdg ()) (ppsi |> evd))
      end
  end

  val >>= = M.bind infixr >>=
  fun =<< (f, m) = m >>= f infix =<<
  fun @@ (f, x) = f x infixr @@
  fun <$> (f, m) = m >>= (fn a => M.pure (f a))
  fun <&> (m1, m2) = m1 >>= (fn a1 => m2 >>= (fn a2 => M.pure (a1, a2)))
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

  fun tactic env : mlterm -> V.value M.m =
    fn ML.VAR x => M.pure @@ Env.lookup env x
     | ML.LET (t, sc) =>
       let
         val (x, tx) = ML.unscope sc
       in
         tactic env t >>= (fn v => 
           tactic (Env.insert env x v) tx)
       end
     | ML.LAM sc => M.pure @@ V.FUN (sc, env)

     | ML.APP (t1, t2) => app =<< (tactic env t1 <&> tactic env t2)
     | ML.PAIR (t1, t2) => V.PAIR <$> (tactic env t1 <&> tactic env t2)
     | ML.FST t => fst <$> tactic env t
     | ML.SND t => snd <$> tactic env t
     | ML.QUOTE abt => M.pure @@ V.QUOTE abt
     | ML.GOAL => getGoal <$> M.get
     | ML.REFINE ruleName => (fn _ => V.NIL) <$> M.rule (Rules.lookupRule ruleName)
     | ML.EACH ts =>
       let
         val ms = List.map (fn t => (fn _ => ()) <$> tactic env t) ts
       in
         (fn _ => V.NIL) <$> M.fork ms
       end

  and app (V.FUN (sc, env), v) =
    let
      val (x, tx) = ML.unscope sc
      val env' = Env.insert env x v
    in
      tactic env' tx
    end

end