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
    type 'a m = names * jdg state -> int * (jdg * 'a) state

    fun isjdg () : (jdg * 'a) isjdg =
      {sort = #sort Lcf.isjdg o #1,
       subst = fn env => fn (j, n) => (#subst Lcf.isjdg env j, n),
       ren = fn ren => fn (j, n) => (#ren Lcf.isjdg ren j, n)}

    fun pure a (alpha, state) = (0, Lcf.map (fn jdg => (jdg, a)) state)
    fun bind (m : 'a m) (f : 'a -> 'b m) (alpha, state) =
      let
        val (n, state' : (jdg * 'a) Lcf.state) = m (alpha, state)
        val alpha' = UniversalSpread.bite n alpha
        val psi |> evd = Lcf.map (fn (jdg, a) => f a (alpha', Lcf.ret Lcf.isjdg jdg)) state'
        val n = Tl.foldr (fn (_, (n', _), n) => Int.max (n', n)) 0 psi
        val psi' = Tl.map (fn (n, j) => j) psi
      in
        (n, mul (isjdg ()) (psi' |> evd))
      end

    fun map (f : 'a -> 'b) (m : 'a m) = bind m (pure o f)

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

    (* Move to LCF library somehow *)
    fun fork ms (alpha, psi |> evd) =
      let
        open Lcf.Tl
        open ConsView
        fun go rho n (r : (jdg * unit) state telescope) =
          fn (_, EMPTY) => (n, r)
           | (m :: ms, CONS (x, (jdg, _), psi)) =>
             let
               val (n', tjdg as psix |> vlx) = m (alpha, idn (J.subst rho jdg))
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