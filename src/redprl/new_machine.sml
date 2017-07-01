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

  val step : sign -> stability -> abt machine -> abt machine
end = 
struct
  structure Tm = RedPrlAbt
  structure Syn = Syntax
  

  type sign = Sig.sign

  datatype 'a closure = <: of 'a * environment
  withtype environment = Tm.abt closure Tm.bview Metavar.Ctx.dict * Tm.abt closure Var.Ctx.dict * Tm.param Sym.Ctx.dict

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

  datatype 'a machine = || of 'a closure * stack


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


  fun lookupSym psi x = 
    Sym.Ctx.lookup psi x
    handle Sym.Ctx.Absent => P.ret x

  fun readParam psi : param -> param = 
    P.bind (lookupSym psi)

  fun insertVar x cl (mrho, rho, psi) = 
    (mrho, Var.Ctx.insert rho x cl, psi)

  fun insertMeta meta bcl (mrho, rho, psi) = 
    (Metavar.Ctx.insert mrho meta bcl, rho, psi)

  fun insertSym u r (mrho, rho, psi) = 
    (mrho, rho, Sym.Ctx.insert psi u r)

  (* Feel free to try and make more efficient *)
  fun forceClosure (tm <: (env as (mrho, rho, psi))) = 
    case infer tm of
       (`x, _) =>
         (case Var.Ctx.find rho x of 
             SOME cl => forceClosure cl
           | NONE => tm)
     | (x $# (ps, ms), tau) => 
         (case Metavar.Ctx.find mrho x of 
             SOME ((us, xs) \ cl) =>
               let
                 val m' = forceClosure cl
                 val rho' = ListPair.foldl (fn (x, n, rho) => Var.Ctx.insert rho x (n <: env)) rho (xs, ms)
                 val psi' = ListPair.foldl (fn (u, (r, _), psi) => Sym.Ctx.insert psi u (readParam psi r)) psi (us, ps)
               in
                 forceClosure (m' <: (mrho, rho', psi'))
               end
           | NONE =>
               let
                 val ps' = List.map (fn (r, sigma) => (readParam psi r, sigma)) ps
                 val ms' = List.map (forceClosure o (fn m => m <: env)) ms
               in
                 check (x $# (ps', ms'), tau)
               end)
     | (theta $ es, _) =>
         let
           val theta' = Tm.O.map (lookupSym psi) theta
           val es' = List.map (mapBind (forceClosure o (fn m => m <: env))) es
         in
           theta' $$ es'
         end


  fun dimensionsEqual (_, _, psi) (r1, r2) = 
    P.eq Sym.eq (readParam psi r1, readParam psi r2)

  fun findTrueEquationIndex env = 
    let
      fun aux i [] = NONE
        | aux i ((r,r') :: eqs) =
          if dimensionsEqual env (r, r') then 
            SOME i
          else 
            aux (i + 1) eqs
    in
      aux 0
    end

  fun stepView sign stability tau = 
    fn `x <: (mrho, rho, psi) || stk =>
       (Var.Ctx.lookup rho x || stk
        handle Var.Ctx.Absent => raise Neutral (VAR x))
     | (tm as (_ $# _)) <: env || stk =>
         forceClosure (check (tm, tau) <: env) <: env || stk

     | O.POLY (O.CUST (opid, ps, _)) $ args <: env || stk => 
       let
         val (mrho, rho, psi) = env
         val entry as {state,...} = Sig.lookup sign opid
         val term = Sig.extract state
         val (mrho', psi') = Sig.applyCustomOperator entry (List.map #1 ps) args
         val mrho'' = Metavar.Ctx.union mrho (Metavar.Ctx.map ((fn (us,xs) \ m => (us,xs) \ (m <: env)) o outb) mrho') (fn _ => raise Fail "Duplicated metavariables")
         val psi'' = raise Match
       in
         term <: (mrho'', rho, psi'') || stk
       end

     | O.POLY (O.COE dir) $ [([u], _) \ a, _ \ coercee] <: env || stk =>
       a <: env || COE (dir, (u, HOLE), coercee) <: env :: stk
     | O.POLY (O.HCOM (dir, eqs)) $ (_ \ a :: _ \ cap :: tubes) <: env || stk =>
       a <: env || HCOM (dir, HOLE, cap, ListPair.map (fn (eq, ([u],_) \ n) => (eq, (u,n))) (eqs, tubes)) <: env :: stk

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

     | O.POLY (O.FCOM (dir, eqs)) $ (_ \ cap :: tubes) <: env || stk =>
       if dimensionsEqual env dir then 
         cap <: env || stk
       else if stability = NOMINAL then 
         case (findTrueEquationIndex env eqs, stk) of 
            (SOME i, _) =>
              let
                val (_, r') = dir
                val ([u], _) \ n = List.nth (tubes, i)
                val env' = insertSym u (readParam (#3 env) r') env
              in
                n <: env' || stk
              end
          | (NONE, []) => raise Final
          | (NONE, W_IF ((x,a), HOLE, mt, mf) <: env' :: stk) => ?todo
          | _ => ?todo

       else
         raise Unstable

     (* TODO: fcom stepping rules *)

     | O.MONO O.AP $ [_ \ m, _ \ n] <: env || stk =>
       m <: env || APP (HOLE, n) <: env :: stk
     | O.MONO O.LAM $ [(_, [x]) \ mx] <: (mrho, rho, psi) || APP (HOLE, n) <: env' :: stk =>
       mx <: (mrho, Var.Ctx.insert rho x (n <: env'), psi) || stk

     | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] <: env || COE ((r,r'), (u, HOLE), coercee) <: env' :: stk =>
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
         lam <: env'' || stk
       end

     | O.MONO O.DFUN $ [_ \ a, (_,[x]) \ bx] <: env || HCOM (dir, HOLE, cap, tubes) <: env' :: stk =>
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
         lam <: env'' || stk
       end

     | O.MONO O.FST $ [_ \ m] <: env || stk =>
        m <: env || FST HOLE <: env :: stk
     | O.MONO O.SND $ [_ \ m] <: env || stk => 
        m <: env || SND HOLE <: env :: stk

     | O.MONO O.PAIR $ [_ \ m1, _] <: env || FST HOLE <: _ :: stk => 
        m1 <: env || stk
     | O.MONO O.PAIR $ [_, _ \ m2] <: env || SND HOLE <: _ :: stk =>
        m2 <: env || stk
    
     | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] <: env || COE ((r,r'), (u, HOLE), coercee) <: env' :: stk => 
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
         pair <: env'' || stk
       end

     | O.MONO O.DPROD $ [_ \ a, (_,[x]) \ bx] <: env || HCOM ((r,r'), HOLE, cap, tubes) <: env' :: stk => 
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
         pair <: env''' || stk
       end


     | _ => raise Final

  fun step sign stability (tm <: env || stk) =
    let
      val (view, tau) = infer tm
    in
      stepView sign stability tau (view <: env || stk)
    end
end