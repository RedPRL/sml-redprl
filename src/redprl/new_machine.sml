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
  exception Stuck

  val init : abt -> abt machine
  val step : sign -> stability -> abt machine -> abt machine
end = 
struct
  structure Tm = RedPrlAbt
  structure Syn = Syntax
  structure SymSet = SplaySet (structure Elem = Sym.Ord)
  
  type sign = Sig.sign

  fun @@ (f, x) = f x
  infixr @@

  infix 6 <:
  infix 3 ||

  open Tm infix 7 $ $$ $# infix 6 \
  structure O = RedPrlOpData
  structure P = struct open RedPrlParameterTerm RedPrlSortData RedPrlParamData end

  type tube = symbol O.equation * (symbol * abt)
  datatype hole = HOLE
  datatype frame =
     APP of hole * abt
   | HCOM of symbol O.dir * hole * abt * tube list
   | COE of symbol O.dir * (symbol * hole) * abt
   | FST of hole
   | SND of hole
   | W_IF of (variable * abt) * hole * abt * abt
   | S1_REC of (variable * abt) * hole * abt * (symbol * abt)
   | IF of hole * abt * abt
   | PATH_AP of hole * symbol P.t
   | NAT_REC of hole * abt * (variable * variable * abt)
   | INT_REC of hole * (variable * variable * abt) * abt * (variable * variable * abt)

  type stack = frame list
  type bound_syms = SymSet.set

  datatype 'a machine = || of 'a * (bound_syms * stack)


  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of variable
   | METAVAR of metavariable

  exception Neutral of blocker
  exception Unstable
  exception Final
  exception Stuck

  val todo = Fail "TODO"
  fun ?e = raise e

  (* Is it safe to observe the identity of a dimension? *)
  fun dimensionSafeToObserve syms r = 
    case r of 
       P.VAR x => SymSet.member syms x
     | _ => true

  fun dimensionsEqual stability syms (r1, r2) = 
    (* If two dimensions are equal, then no substitution can ever change that. *)
    if P.eq Sym.eq (r1, r2) then 
      true
    else
      (* On the other hand, if they are not equal, this observation may not commute with cubical substitutions. *)
      case stability of 
          (* An observation of apartness is stable under permutations. *)
          NOMINAL => false
          (* An observation of apartness is only stable if one of the compared dimensions is bound. *)
        | CUBICAL =>
            if dimensionSafeToObserve syms r1 orelse dimensionSafeToObserve syms r2 then 
              false 
            else
              raise Unstable

  fun findTubeWithTrueEquation stability syms = 
    let
      val rec aux = 
        fn [] => NONE
         | (eq, (u, n)) :: tubes =>
           if dimensionsEqual stability syms eq then 
             SOME (u, n)
           else 
             aux tubes
    in
      aux
    end

  fun mapTubes f : tube list -> tube list = List.map (fn (eq, (u, n)) => (eq, (u, f (u, n))))

  fun zipTubesWith f : symbol O.equation list * abt bview list -> tube list =
    ListPair.map (fn (eq, ([u], _) \ n) => (eq, (u, f (u, n))))

  fun mapTubes_ f = mapTubes (f o #2)
  val zipTubes = zipTubesWith #2

  fun stepFCom stability ({dir = dir as (r, r'), cap, tubes} || (syms, stk)) =
    if dimensionsEqual stability syms dir then 
      cap || (syms, stk)
    else
      case findTubeWithTrueEquation stability syms tubes of
         SOME (u, n) => substSymbol (r', u) n || (syms, stk)
       | NONE =>
         (case stk of
             [] => raise Final
           | W_IF ((x, tyx), HOLE, t, f) :: stk =>
             let
               val u = Sym.named "u"
               val fcomu =
                 Syn.into @@ Syn.FCOM
                   {dir = (r, P.ret u),
                    cap = cap,
                    tubes = tubes}
               fun if_ m = Syn.into @@ Syn.IF ((x, tyx), m, (t, f))
               val com =
                 Syn.into @@ Syn.COM 
                   {dir = dir,
                    ty = (u, substVar (fcomu, x) tyx),
                    cap = if_ cap,
                    tubes = mapTubes_ if_ tubes}
             in
               com || (syms, stk)
             end
           | S1_REC ((x, tyx), HOLE, base, (v, loop)) :: stk => 
             let
               val u = Sym.named "u"
               val fcomu =
                 Syn.into @@ Syn.FCOM
                   {dir = (r, P.ret u),
                    cap = cap,
                    tubes = tubes}
               fun s1rec m = Syn.into @@ Syn.S1_ELIM ((x, tyx), m, (base, (v, loop)))
               val com =
                 Syn.into @@ Syn.COM 
                   {dir = dir,
                    ty = (u, substVar (fcomu, x) tyx),
                    cap = s1rec cap,
                    tubes = mapTubes_ s1rec tubes}
             in
               com || (syms, stk)
             end
           | _ => raise Stuck)

  fun stepView sign stability tau =
    fn `x || stk => raise Neutral (VAR x)
     | x $# (rs, ms) || stk => raise Neutral (METAVAR x)

     | O.POLY (O.HCOM (dir, eqs)) $ (_ \ ty :: _ \ cap :: tubes) || (syms, stk) => ty || (syms, HCOM (dir, HOLE, cap, zipTubes (eqs, tubes)) :: stk)
     | O.POLY (O.COE dir) $ [([u], _) \ ty, _ \ coercee] || (syms, stk) => ty || (SymSet.insert syms u, COE (dir, (u, HOLE), coercee) :: stk)
     | O.POLY (O.COM (dir, eqs)) $ (([u], _) \ ty :: _ \ cap :: tubes) || (syms, stk) =>
       let
         val (r, r') = dir
         fun coe s m = 
           Syn.into @@ Syn.COE
             {dir = (s, r'),
              ty = (u, ty),
              coercee = m}
          val hcom =
            Syn.into @@ Syn.HCOM
              {dir = dir,
               ty = substSymbol (r', u) ty,
               cap = coe r cap,
               tubes = zipTubesWith (fn (u, n) => coe (P.ret u) n) (eqs, tubes)}
       in
         hcom || (syms, stk)
       end

     | O.POLY (O.FCOM (dir, eqs)) $ (_ \ cap :: tubes) || (syms, stk) =>
       stepFCom stability ({dir = dir, cap = cap, tubes = zipTubes (eqs, tubes)} || (syms, stk))

     | O.MONO O.LAM $ _ || (_, []) => raise Final
     | O.MONO O.DFUN $ _ || (_, []) => raise Final

     | O.MONO O.AP $ [_ \ m, _ \ n] || (syms, stk) => m || (syms, APP (HOLE, n) :: stk)
     | O.MONO O.LAM $ [(_,[x]) \ m] || (syms, APP (HOLE, n) :: stk) => substVar (n, x) m || (syms, stk)
     | O.MONO O.DFUN $ [_ \ tyA, (_,[x]) \ tyBx] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val xtm = Syn.into @@ Syn.VAR (x, O.EXP)
         fun apx n = Syn.into @@ Syn.AP (n, xtm)
         val hcomx =
           Syn.into @@ Syn.HCOM
             {dir = dir,
              ty = tyBx,
              cap = apx cap,
              tubes = mapTubes_ apx tubes}
         val lambda = Syn.into @@ Syn.LAM (x, hcomx)
       in
         lambda || (syms, stk)
       end
     | O.MONO O.DFUN $ [_ \ tyA, (_,[x]) \ tyBx] || (syms, COE (dir, (u, HOLE), coercee) :: stk) =>
       let
         val (r, r') = dir
         val xtm = Syn.into @@ Syn.VAR (x, O.EXP)
         fun xcoe s =
           Syn.into @@ Syn.COE
             {dir = (r', s),
              ty = (u, tyA),
              coercee = xtm}
          val lambda =
            Syn.into @@ Syn.LAM (x,
              Syn.into @@ Syn.COE 
                {dir = dir,
                 ty = (u, substVar (xcoe (P.ret u), x) tyBx),
                 coercee = Syn.into @@ Syn.AP (coercee, xcoe r)})
       in
         lambda || (SymSet.remove syms u, stk)
       end

     | O.MONO O.PAIR $ _ || (_, []) => raise Final
     | O.MONO O.DPROD $ _ || (_, []) => raise Final

     | O.MONO O.FST $ [_ \ m] || (syms, stk) => m || (syms, FST HOLE :: stk)
     | O.MONO O.SND $ [_ \ m] || (syms, stk) => m || (syms, SND HOLE :: stk)
     | O.MONO O.PAIR $ [_ \ m, _ \ _] || (syms, FST HOLE :: stk) => m || (syms, stk)
     | O.MONO O.PAIR $ [_ \ _, _ \ n] || (syms, SND HOLE :: stk) => n || (syms, stk)
     | O.MONO O.DPROD $ [_ \ tyA, (_, [x]) \ tyBx] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val (r, r') = dir
         fun left s = 
           Syn.into @@ Syn.HCOM
             {dir = (r, s),
              ty = tyA,
              cap = Syn.into @@ Syn.FST cap,
              tubes = mapTubes_ (Syn.into o Syn.FST) tubes}
          val u = Sym.named "u"
          val right = 
            Syn.into @@ Syn.COM
              {dir = dir,
               ty = (u, substVar (left (P.ret u), x) tyBx),
               cap = Syn.into @@ Syn.SND cap,
               tubes = mapTubes_ (Syn.into o Syn.SND) tubes}
          val pair = Syn.into @@ Syn.PAIR (left r', right)
       in
         pair || (syms, stk)
       end
     | O.MONO O.DPROD $ [_ \ tyA, (_, [x]) \ tyBx] || (syms, COE (dir, (u, HOLE), coercee) :: stk) =>
       let
         val (r, r') = dir
         fun left s = 
           Syn.into @@ Syn.COE
             {dir = (r, s),
              ty = (u, tyA),
              coercee = Syn.into @@ Syn.FST coercee}
          val right = 
            Syn.into @@ Syn.COE
              {dir = dir,
               ty = (u, substVar (left (P.ret u), x) tyBx),
               coercee = Syn.into @@ Syn.SND coercee}
          val pair = Syn.into @@ Syn.PAIR (left r', right)
       in
         pair || (SymSet.remove syms u, stk)
       end

     | O.MONO O.PATH_ABS $ _ || (_, []) => raise Final
     | O.MONO O.PATH_TY $ _ || (_, []) => raise Final

     | O.POLY (O.PATH_AP r) $ [_ \ m] || (syms, stk) => m || (syms, PATH_AP (HOLE, r) :: stk)
     | O.MONO O.PATH_ABS $ [([u], _) \ m] || (syms, PATH_AP (HOLE, r) :: stk) => substSymbol (r, u) m || (syms, stk)

     | O.MONO O.PATH_TY $ [([u], _) \ tyu, _ \ m0, _ \ m1] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         fun apu m = Syn.into @@ Syn.PATH_AP (m, P.ret u)
         val v = Sym.named "_"
         val hcomu =
           Syn.into @@ Syn.HCOM
             {dir = dir,
              ty = tyu,
              cap = apu cap,
              tubes = ((P.ret u, P.APP P.DIM0), (v, m0)) :: ((P.ret u, P.APP P.DIM1), (v, m1)) :: mapTubes_ apu tubes}
         val abs = Syn.into @@ Syn.PATH_ABS (u, hcomu)
       in
         abs || (syms, stk)
       end
     | O.MONO O.PATH_TY $ [([u], _) \ tyuv, _ \ m0v, _ \ m1v] || (syms, COE (dir, (v, HOLE), coercee) :: stk) =>
       let
         val comu =
           Syn.into @@ Syn.COM
             {dir = dir,
              ty = (v, tyuv),
              cap = Syn.into @@ Syn.PATH_AP (coercee, P.ret u),
              tubes = [((P.ret u, P.APP P.DIM0), (v, m0v)), ((P.ret u, P.APP P.DIM1), (v, m1v))]}
         val abs = Syn.into @@ Syn.PATH_ABS (u, comu)
       in
         abs || (SymSet.remove syms v, stk)
       end

     | O.MONO O.NAT $ _ || (_, []) => raise Final
     | O.MONO O.ZERO $ _ || (_, []) => raise Final
     | O.MONO O.SUCC $ _ || (_, []) => raise Final
     | O.MONO O.NAT_REC $ [_ \ m, _ \ n, (_,[x,y]) \ p] || (syms, stk) => m || (syms, NAT_REC (HOLE, n, (x,y,p)) :: stk)
     | O.MONO O.ZERO $ _ || (syms, NAT_REC (HOLE, zer, _) :: stk) => zer || (syms, stk)
     | O.MONO O.SUCC $ [_ \ n] || (syms, NAT_REC (HOLE, zer, (x,y, succ)) :: stk) =>
       let
         val rho = Var.Ctx.insert (Var.Ctx.singleton x n) y @@ Syn.into @@ Syn.NAT_REC (n, (zer, (x,y,succ)))
       in
         substVarenv rho succ || (syms, stk)
       end
     | O.MONO O.NAT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => cap || (syms, stk)
     | O.MONO O.NAT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => coercee || (SymSet.remove syms u, stk)

     | O.MONO O.INT $ _ || (_, []) => raise Final
     | O.MONO O.NEGSUCC $ _ || (_, []) => raise Final
     | O.MONO O.INT_REC $ [_ \ m, (_,[x,y]) \ p, _ \ q, (_,[x',y']) \ r] || (syms, stk) => m || (syms, INT_REC (HOLE, (x,y,p), q, (x',y',r)) :: stk) 
     | O.MONO O.ZERO $ _ || (syms, INT_REC (HOLE, _, q, _) :: stk) => q || (syms, stk)
     | O.MONO O.SUCC $ [_ \ n] || (syms, INT_REC (HOLE, (x,y,p), zer, (x',y',q)) :: stk) => 
       let
         val rho = Var.Ctx.insert (Var.Ctx.singleton x' n) y' @@ Syn.into @@ Syn.INT_REC (n, ((x,y,p), zer, (x',y',q)))
       in
         substVarenv rho q || (syms, stk)
       end
     | O.MONO O.NEGSUCC $ [_ \ n] || (syms, INT_REC (HOLE, (x,y,p), zer, (x',y',q)) :: stk) => 
       let
         val rho = Var.Ctx.insert (Var.Ctx.singleton x n) y @@ Syn.into @@ Syn.INT_REC (n, ((x,y,p), zer, (x',y',q)))
       in
         substVarenv rho p || (syms, stk)
       end
     | O.MONO O.INT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => cap || (syms, stk)
     | O.MONO O.INT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => coercee || (SymSet.remove syms u, stk)


  fun step sign stability (tm || stk) =
    let
      val (view, tau) = infer tm
    in
      stepView sign stability tau (view || stk)
    end

  fun init tm = 
    tm || (SymSet.empty, [])
end