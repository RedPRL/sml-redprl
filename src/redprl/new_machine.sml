functor NewMachine (Sig : MINI_SIGNATURE) :
sig
  type sign = Sig.sign
  type abt = RedPrlAbt.abt
  type 'a machine

  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable

  exception Neutral of blocker
  exception Unstable
  exception Final

  val init : abt -> abt machine
  val step : sign -> stability -> abt machine -> abt machine
end = 
struct
  structure Tm = RedPrlAbt
  structure Syn = Syntax
  structure SymSet = SplaySet (structure Elem = Sym.Ord)
  
  type sign = Sig.sign
  open Closure

  fun @@ (f, x) = f x
  infixr @@

  infix 6 <:
  infix 3 ||


  open Tm infix 7 $ $$ $# infix 6 \
  structure O = RedPrlOpData
  structure P = struct open RedPrlParameterTerm RedPrlSortData end

  datatype hole = HOLE
  datatype continuation =
     APP of hole * abt
   | HCOM of symbol O.dir * hole * abt * (symbol O.equation * (symbol * abt)) list
   | COE of symbol O.dir * (symbol * hole) * abt
   | FST of hole
   | SND of hole
   | W_IF of (variable * abt) * hole * abt * abt
   | IF of hole * abt * abt

  type frame = continuation closure
  type stack = frame list
  type bound_syms = SymSet.set

  datatype 'a machine = || of 'a closure * (bound_syms * stack)


  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of variable
   | METAVAR of metavariable

  exception Neutral of blocker
  exception Unstable
  exception Final

  val todo = Fail "TODO"
  fun ?e = raise e

  (* Is it safe to observe the identity of a dimension? *)
  fun dimensionSafeToObserve syms r = 
    case r of 
       P.VAR x => SymSet.member syms x
     | _ => true

  fun dimensionsEqual stability syms env (r1, r2) = 
    let
      val r1' = Env.forceParam env r1
      val r2' = Env.forceParam env r2
    in
      (* If two dimensions are equal, then no substitution can ever change that. *)
      if P.eq Sym.eq (r1', r2') then 
        true
      else
        (* On the other hand, if they are not equal, this observation may not commute with cubical substitutions. *)
        case stability of 
           (* An observation of apartness is stable under permutations. *)
           NOMINAL => false
           (* An observation of apartness is only stable if one of the compared dimensions is bound. *)
         | CUBICAL =>
             if dimensionSafeToObserve syms r1' orelse dimensionSafeToObserve syms r2' then 
               false 
             else
               raise Unstable
    end

  fun findTrueEquationIndex stability syms env = 
    let
      fun aux i [] = NONE
        | aux i ((r,r') :: eqs) =
          if dimensionsEqual stability syms env (r, r') then 
            SOME i
          else 
            aux (i + 1) eqs
    in
      aux 0
    end

  fun stepView sign stability tau =
    fn `x <: env || stk =>
       Closure.variable (x, tau) env || stk (* TODO: this should raise Neutral or something?? *)
     | x $# (rs, ms) <: env || stk =>
       Closure.metavariable (x, rs, ms, tau) env || stk

     | O.POLY (O.CUST (opid, ps, _)) $ args <: env || stk => 
       let
         val entry as {state,...} = Sig.lookup sign opid
         val term = Sig.extract state
         val (mrho, psi) = Sig.applyCustomOperator entry (List.map #1 ps) args
         val env' =
           Metavar.Ctx.foldr
             (fn (x, abs, env') => Env.insertMeta x (mapBind (fn m => m <: env) (outb abs)) env')
             env
             mrho
         val env'' = 
           Sym.Ctx.foldr 
             (fn (u, r, env'') => Env.insertSym u r env'')
             env'
             psi
       in
         term <: env'' || stk
       end
(*
     | O.POLY (O.COE dir) $ [([u], _) \ a, _ \ coercee] <: env || (syms, stk) =>
       a <: env || (SymSet.insert syms u, COE (dir, (u, HOLE), coercee) <: env :: stk)
     | O.POLY (O.HCOM (dir, eqs)) $ (_ \ a :: _ \ cap :: tubes) <: env || (syms, stk) =>
       a <: env || (syms, HCOM (dir, HOLE, cap, ListPair.map (fn (eq, ([u],_) \ n) => (eq, (u,n))) (eqs, tubes)) <: env :: stk)

     | O.POLY (O.COM ((r,r'), eqs)) $ (([u],_) \ a :: _ \ cap :: tubes) <: env || stk => 
       let
         fun makeTube (eq, ([v],_) \ n) = 
           (eq, (v, Syn.into @@ Syn.COE
             {dir = (P.ret v, r'),
              ty = (v, a),
              coercee = n}))

         val hcom = 
           Syn.into @@ Syn.HCOM
             {dir = (r, r'),
              ty = a,
              cap = Syn.into @@ Syn.COE
                {dir = (r, r'),
                 ty = (u, a),
                 coercee = cap},
              tubes = ListPair.map makeTube (eqs, tubes)}

          val env' = insertSym u (readParam (#3 env) r') env
       in
         hcom <: env' || stk
       end

     | O.POLY (O.FCOM (dir, eqs)) $ (_ \ cap :: tubes) <: env || (syms, stk) =>
       if dimensionsEqual stability syms env dir then 
         cap <: env || (syms, stk)
       (* TODO: be less conservative, use 'syms' as a weapon *)
       else
         (case (findTrueEquationIndex stability syms env eqs, stk) of 
             (SOME i, _) =>
               let
                 val (_, r') = dir
                 val ([u], _) \ n = List.nth (tubes, i)
                 val env' = insertSym u (readParam (#3 env) r') env
               in
                 n <: env' || (syms, stk)
               end
           | (NONE, []) => raise Final
           | (NONE, W_IF ((x,a), HOLE, mt, mf) <: env' :: stk) => ?todo
           | _ => ?todo)

     (* TODO: fcom stepping rules *)

     | O.MONO O.AP $ [_ \ m, _ \ n] <: env || (syms, stk) =>
       m <: env || (syms, APP (HOLE, n) <: env :: stk)
     | O.MONO O.LAM $ [(_, [x]) \ mx] <: (mrho, rho, psi) || (syms, APP (HOLE, n) <: env' :: stk) =>
       mx <: (mrho, Var.Ctx.insert rho x (n <: env'), psi) || (syms, stk)

     | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] <: env || (us, COE ((r,r'), (u, HOLE), coercee) <: env' :: stk) =>
       let
         val metaX = Metavar.named "X"
         val metaY = Metavar.named "Y"
         val metaZ = Metavar.named "Z"
         val xtm = check (`x, O.EXP)
         val uprm = (P.ret u, P.DIM)
         val y = Var.named "y"
         val ytm = check (`y, O.EXP)

         val lam =
           Syn.into @@ Syn.LAM (x, 
            Syn.into @@ Syn.COE
              {dir = (r,r'),
               ty = (u, check (metaX $# ([uprm], [xtm]), O.EXP)),
               coercee = 
                 Syn.into @@ Syn.AP
                   (coercee,
                    Syn.into @@ Syn.COE
                      {dir = (r', r),
                       ty = (u, check (metaY $# ([uprm],[]), O.EXP)),
                       coercee = check (metaY $# ([uprm],[]), O.EXP)})})

         val metaYCl = ([u], []) \ (a <: env)

         val coeyCl = 
           Syn.into 
             (Syn.COE
               {dir = (r', P.ret u),
                ty = (u, check (metaZ $# ([uprm],[]), O.EXP)),
                coercee = ytm})
             <: insertMeta metaZ (([u],[]) \ (a <: env)) env'

         val metaXCl = ([u], [y]) \ (bx <: insertVar x coeyCl env)
         val env'' = 
           insertMeta metaY metaYCl @@ 
             insertMeta metaX metaXCl env'
       in
         lam <: env'' || (SymSet.remove us u, stk)
       end

     | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] <: env || (syms, HCOM (dir, HOLE, cap, tubes) <: env' :: stk) =>
       let
         val metaX = Metavar.named "X"
         val env'' = insertMeta metaX (([],[x]) \ (bx <: env)) env'
         val xtm = check (`x, O.EXP)
         val hcom =
           Syn.into @@ Syn.HCOM 
             {dir = dir,
              ty = check (metaX $# ([],[xtm]), O.EXP),
              cap = Syn.into @@ Syn.AP (cap, xtm),
              tubes = List.map (fn (eq, (u, n)) => (eq, (u, Syn.into @@ Syn.AP (n, xtm)))) tubes}

         val lam = Syn.into @@ Syn.LAM (x, hcom)
       in
         lam <: env'' || (syms, stk)
       end

     | O.MONO O.FST $ [_ \ m] <: env || (syms, stk) =>
        m <: env || (syms, FST HOLE <: env :: stk)
     | O.MONO O.SND $ [_ \ m] <: env || (syms, stk) => 
        m <: env || (syms, SND HOLE <: env :: stk)

     | O.MONO O.PAIR $ [_ \ m1, _] <: env || (syms, FST HOLE <: _ :: stk) => 
        m1 <: env || (syms, stk)
     | O.MONO O.PAIR $ [_, _ \ m2] <: env || (syms, SND HOLE <: _ :: stk) =>
        m2 <: env || (syms, stk)
    
     | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] <: env || (syms, COE ((r,r'), (u, HOLE), coercee) <: env' :: stk) => 
       let
         val metaX = Metavar.named "X"
         val metaY = Metavar.named "Y"
         val uprm = (P.ret u, P.DIM)
         val proj1 =
           Syn.into @@ Syn.COE
             {dir = (r, r'),
              ty = (u, check (metaX $# ([uprm], []), O.EXP)),
              coercee = Syn.into @@ Syn.FST coercee}
         fun proj2 s = 
           Syn.into @@ Syn.COE
             {dir = (r, s),
              ty = (u, check (metaY $# ([uprm], []), O.EXP)),
              coercee = Syn.into @@ Syn.SND coercee}

         val metaXCl = ([u],[]) \ (a <: env)
         val metaYCl = ([u],[]) \ (bx <: insertVar x (proj2 (P.ret u) <: insertMeta metaX metaXCl env) env)
         val env'' = insertMeta metaX metaXCl (insertMeta metaY metaYCl env')

         val pair = Syn.into @@ Syn.PAIR (proj1, proj2 r')
       in
         pair <: env'' || (SymSet.remove syms u, stk)
       end

     | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] <: env || (syms, HCOM ((r,r'), HOLE, cap, tubes) <: env' :: stk) => 
       let
         val metaX = Metavar.named "X"
         val metaY = Metavar.named "Y"
         val xtm = check (`x, O.EXP)

         fun proj1 s = 
           Syn.into @@ Syn.HCOM 
             {dir = (r, s),
              ty = check (metaX $# ([],[]), O.EXP),
              cap = Syn.into @@ Syn.FST cap,
              tubes = List.map (fn (eq, (u, n)) => (eq, (u, Syn.into @@ Syn.FST n))) tubes}

         val v = Sym.named "v"

         val proj2 = 
           Syn.into @@ Syn.COM
             {dir = (r, r'),
              ty = (v, check (metaY $# ([(P.ret v, P.DIM)], []), O.EXP)),
              cap = Syn.into @@ Syn.SND cap,
              tubes = List.map (fn (eq, (u, n)) => (eq, (u, Syn.into @@ Syn.SND n))) tubes}

         val pair = Syn.into @@ Syn.PAIR (proj1 r', proj2)

         val env'' = insertMeta metaX (([],[]) \ (a <: env)) env'
         val metaYCl = ([v],[]) \ (bx <: (insertVar x (proj1 (P.ret v) <: env'') env))
         val env''' = insertMeta metaY metaYCl env''
       in
         pair <: env''' || (syms, stk)
       end


     | _ => raise Final *)

  fun step sign stability (tm <: env || stk) =
    let
      val (view, tau) = infer tm
    in
      stepView sign stability tau (view <: env || stk)
    end

  fun init tm = 
    tm <: Env.empty || (SymSet.empty, [])
end