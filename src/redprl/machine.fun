functor RedPrlMachine (Sig : MINI_SIGNATURE) : REDPRL_MACHINE =
struct
  structure Tm = RedPrlAbt
  structure Syn = Syntax
  structure SymSet = SplaySet (structure Elem = Sym.Ord)
  
  type sign = Sig.sign
  type opid = Sig.opid

  fun @@ (f, x) = f x
  infixr @@

  infix 6 <:
  infix 3 ||

  open Tm infix 7 $ $$ $# infix 6 \
  structure O = RedPrlOpData
  structure P = struct open RedPrlParameterTerm RedPrlSortData RedPrlParamData end

  structure Tac =
  struct
    val autoStep = O.MONO O.RULE_AUTO_STEP $$ []
    val auto = O.MONO O.MTAC_AUTO $$ []

    fun elim (u, tau) =
      O.POLY (O.RULE_ELIM (u, tau)) $$ []

    fun all t =
      O.MONO O.MTAC_ALL $$ [([],[]) \ t]

    fun each ts =
      O.MONO (O.MTAC_EACH (List.length ts)) $$ List.map (fn t => ([],[]) \ t) ts

    fun seq mt1 bs mt2 =
      let
        val (us, sorts) = ListPair.unzip bs
      in
        O.MONO (O.MTAC_SEQ sorts) $$ [([],[]) \ mt1, (us, []) \ mt2]
      end

    fun mtac mt =
      O.MONO O.TAC_MTAC $$ [([],[]) \ mt]


    fun mtry mt =
      O.MONO O.MTAC_ORELSE $$ [([],[]) \ mt, ([],[]) \ all (O.MONO O.RULE_ID $$ [])]

    fun try t =
      mtac (mtry (all t))

    fun mprogress mt =
      O.MONO O.MTAC_PROGRESS $$ [([],[]) \ mt]

    fun multirepeat mt =
      O.MONO O.MTAC_REPEAT $$ [([],[]) \ mt]

    fun cut jdg =
      O.MONO O.RULE_CUT $$ [([],[]) \ jdg]

    val autoTac = mtac auto

    fun prim name = 
      O.MONO (O.RULE_PRIM name) $$ []
  end


  type tube = symbol O.equation * (symbol * abt)
  datatype hole = HOLE
  datatype frame =
     APP of hole * abt
   | HCOM of symbol O.dir * hole * abt * tube list
   | COE of symbol O.dir * (symbol * hole) * abt
   | FST of hole
   | SND of hole
   | WIF of (variable * abt) * hole * abt * abt
   | S1_REC of (variable * abt) * hole * abt * (symbol * abt)
   | IF of hole * abt * abt
   | PATH_APP of hole * symbol P.t
   | NAT_REC of hole * abt * (variable * variable * abt)
   | INT_REC of hole * (variable * variable * abt) * abt * (variable * variable * abt)
   | PROJ of string * hole
   | TUPLE_UPDATE of string * abt * hole

  type stack = frame list
  type bound_syms = SymSet.set

  datatype 'a machine = || of 'a * (bound_syms * stack)

  val todo = Fail "TODO"
  fun ?e = raise e

  local
    fun plug m = 
      fn APP (HOLE, n) => Syn.into @@ Syn.APP (m, n)
       | HCOM (dir, HOLE, cap, tubes) => Syn.into @@ Syn.HCOM {dir = dir, ty = m, cap = cap, tubes = tubes}
       | COE (dir, (u, HOLE), coercee) => Syn.into @@ Syn.COE {dir = dir, ty = (u, m), coercee = coercee}
       | FST HOLE => Syn.into @@ Syn.FST m
       | SND HOLE => Syn.into @@ Syn.SND m
       | IF (HOLE, t, f) => Syn.into @@ Syn.IF (m, (t, f))
       | WIF ((x, tyx), HOLE, t, f) => Syn.into @@ Syn.WIF ((x, tyx), m, (t, f))
       | S1_REC ((x, tyx), HOLE, base, (u, loop)) => Syn.into @@ Syn.S1_REC ((x, tyx), m, (base, (u, loop)))
       | PATH_APP (HOLE, r) => Syn.into @@ Syn.PATH_APP (m, r)
       | NAT_REC (HOLE, zer, (x, y, succ)) => Syn.into @@ Syn.NAT_REC (m, (zer, (x, y, succ)))
       | INT_REC (HOLE, (x,y,negsucc), zer, (x',y',succ)) => Syn.into @@ Syn.INT_REC (m, ((x,y,negsucc), zer, (x',y',succ)))
       | PROJ (lbl, HOLE) => Syn.into @@ Syn.PROJ (lbl, m)
       | TUPLE_UPDATE (lbl, n, HOLE) => Syn.into @@ Syn.TUPLE_UPDATE ((lbl, m), m)
  in
    fun unload (m || (syms, stk)) = 
      case stk of
         [] => m
       | k :: stk => unload @@ plug m k || (syms, stk)
  end

  datatype stability = 
     CUBICAL
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable
   | OPERATOR of RedPrlAbt.symbol

  structure Unfolding = 
  struct
    type regime = opid -> bool

    fun default sign opid = 
      let
        val {spec, ...} = Sig.lookup sign opid
        open RedPrlSequent infix >>
      in
        case spec of
          _ >> RedPrlCategoricalJudgment.TRUE _ => false
        | _ => true
      end

    fun never _ = false
    fun always _ = true
  end

  exception Neutral of blocker
  exception Unstable
  exception Final
  exception Stuck

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

  datatype 'a action = 
     COMPAT of 'a
   | CRITICAL of 'a
   | STEP of 'a

  fun stepFCom stability ({dir = dir as (r, r'), cap, tubes} || (syms, stk)) =
    if dimensionsEqual stability syms dir then 
      STEP @@ cap || (syms, stk)
    else
      case findTubeWithTrueEquation stability syms tubes of
         SOME (u, n) => STEP @@ substSymbol (r', u) n || (syms, stk)
       | NONE =>
         (case stk of
             [] => raise Final
           | WIF ((x, tyx), HOLE, t, f) :: stk =>
             let
               val u = Sym.named "u"
               val fcomu =
                 Syn.into @@ Syn.FCOM
                   {dir = (r, P.ret u),
                    cap = cap,
                    tubes = tubes}
               fun if_ m = Syn.into @@ Syn.WIF ((x, tyx), m, (t, f))
               val com =
                 Syn.into @@ Syn.COM 
                   {dir = dir,
                    ty = (u, substVar (fcomu, x) tyx),
                    cap = if_ cap,
                    tubes = mapTubes_ if_ tubes}
             in
               CRITICAL @@ com || (syms, stk)
             end
           | S1_REC ((x, tyx), HOLE, base, (v, loop)) :: stk => 
             let
               val u = Sym.named "u"
               val fcomu =
                 Syn.into @@ Syn.FCOM
                   {dir = (r, P.ret u),
                    cap = cap,
                    tubes = tubes}
               fun s1rec m = Syn.into @@ Syn.S1_REC ((x, tyx), m, (base, (v, loop)))
               val com =
                 Syn.into @@ Syn.COM 
                   {dir = dir,
                    ty = (u, substVar (fcomu, x) tyx),
                    cap = s1rec cap,
                    tubes = mapTubes_ s1rec tubes}
             in
               CRITICAL @@ com || (syms, stk)
             end
           | _ => raise Stuck)

  fun stepView sign stability unfolding tau =
    fn `x || _ => raise Neutral (VAR x)
     | x $# (rs, ms) || _ => raise Neutral (METAVAR x)

     | O.POLY (O.CUST (opid, ps, _)) $ args || (syms, stk) =>
       if not (unfolding opid) then raise Neutral (OPERATOR opid) else
       let
         val entry as {state, ...} = Sig.lookup sign opid
         val (mrho, srho) = Sig.applyCustomOperator entry (List.map #1 ps) args
         val term = substSymenv srho (substMetaenv mrho (Sig.extract state))
       in
         STEP @@ term || (syms, stk)
       end  

     | O.POLY (O.HCOM (dir, eqs)) $ (_ \ ty :: _ \ cap :: tubes) || (syms, stk) => COMPAT @@ ty || (syms, HCOM (dir, HOLE, cap, zipTubes (eqs, tubes)) :: stk)
     | O.POLY (O.COE dir) $ [([u], _) \ ty, _ \ coercee] || (syms, stk) => COMPAT @@ ty || (SymSet.insert syms u, COE (dir, (u, HOLE), coercee) :: stk)
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
         STEP @@ hcom || (syms, stk)
       end

     | O.POLY (O.FCOM (dir, eqs)) $ (_ \ cap :: tubes) || (syms, stk) =>
       stepFCom stability ({dir = dir, cap = cap, tubes = zipTubes (eqs, tubes)} || (syms, stk))

     | O.MONO O.LAM $ _ || (_, []) => raise Final
     | O.MONO O.DFUN $ _ || (_, []) => raise Final

     | O.MONO O.APP $ [_ \ m, _ \ n] || (syms, stk) => COMPAT @@ m || (syms, APP (HOLE, n) :: stk)
     | O.MONO O.LAM $ [(_,[x]) \ m] || (syms, APP (HOLE, n) :: stk) => CRITICAL @@ substVar (n, x) m || (syms, stk)
     | O.MONO O.DFUN $ [_ \ tyA, (_,[x]) \ tyBx] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val xtm = Syn.into @@ Syn.VAR (x, O.EXP)
         fun apx n = Syn.into @@ Syn.APP (n, xtm)
         val hcomx =
           Syn.into @@ Syn.HCOM
             {dir = dir,
              ty = tyBx,
              cap = apx cap,
              tubes = mapTubes_ apx tubes}
         val lambda = Syn.into @@ Syn.LAM (x, hcomx)
       in
         CRITICAL @@ lambda || (syms, stk)
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
                 coercee = Syn.into @@ Syn.APP (coercee, xcoe r)})
       in
         CRITICAL @@ lambda || (SymSet.remove syms u, stk)
       end

     | O.MONO O.PAIR $ _ || (_, []) => raise Final
     | O.MONO O.DPROD $ _ || (_, []) => raise Final

     | O.MONO O.FST $ [_ \ m] || (syms, stk) => COMPAT @@ m || (syms, FST HOLE :: stk)
     | O.MONO O.SND $ [_ \ m] || (syms, stk) => COMPAT @@ m || (syms, SND HOLE :: stk)
     | O.MONO O.PAIR $ [_ \ m, _ \ _] || (syms, FST HOLE :: stk) => CRITICAL @@ m || (syms, stk)
     | O.MONO O.PAIR $ [_ \ _, _ \ n] || (syms, SND HOLE :: stk) => CRITICAL @@ n || (syms, stk)
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
         CRITICAL @@ pair || (syms, stk)
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
         CRITICAL @@ pair || (SymSet.remove syms u, stk)
       end

     | O.MONO O.PATH_ABS $ _ || (_, []) => raise Final
     | O.MONO O.PATH_TY $ _ || (_, []) => raise Final

     | O.POLY (O.PATH_APP r) $ [_ \ m] || (syms, stk) => COMPAT @@ m || (syms, PATH_APP (HOLE, r) :: stk)
     | O.MONO O.PATH_ABS $ [([u], _) \ m] || (syms, PATH_APP (HOLE, r) :: stk) => CRITICAL @@ substSymbol (r, u) m || (syms, stk)

     | O.MONO O.PATH_TY $ [([u], _) \ tyu, _ \ m0, _ \ m1] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         fun apu m = Syn.into @@ Syn.PATH_APP (m, P.ret u)
         val v = Sym.named "_"
         val hcomu =
           Syn.into @@ Syn.HCOM
             {dir = dir,
              ty = tyu,
              cap = apu cap,
              tubes = ((P.ret u, P.APP P.DIM0), (v, m0)) :: ((P.ret u, P.APP P.DIM1), (v, m1)) :: mapTubes_ apu tubes}
         val abs = Syn.into @@ Syn.PATH_ABS (u, hcomu)
       in
         CRITICAL @@ abs || (syms, stk)
       end
     | O.MONO O.PATH_TY $ [([u], _) \ tyuv, _ \ m0v, _ \ m1v] || (syms, COE (dir, (v, HOLE), coercee) :: stk) =>
       let
         val comu =
           Syn.into @@ Syn.COM
             {dir = dir,
              ty = (v, tyuv),
              cap = Syn.into @@ Syn.PATH_APP (coercee, P.ret u),
              tubes = [((P.ret u, P.APP P.DIM0), (v, m0v)), ((P.ret u, P.APP P.DIM1), (v, m1v))]}
         val abs = Syn.into @@ Syn.PATH_ABS (u, comu)
       in
         CRITICAL @@ abs || (SymSet.remove syms v, stk)
       end

     | O.MONO O.NAT $ _ || (_, []) => raise Final
     | O.MONO O.ZERO $ _ || (_, []) => raise Final
     | O.MONO O.SUCC $ _ || (_, []) => raise Final
     | O.MONO O.NAT_REC $ [_ \ m, _ \ n, (_,[x,y]) \ p] || (syms, stk) => COMPAT @@ m || (syms, NAT_REC (HOLE, n, (x,y,p)) :: stk)
     | O.MONO O.ZERO $ _ || (syms, NAT_REC (HOLE, zer, _) :: stk) => CRITICAL @@ zer || (syms, stk)
     | O.MONO O.SUCC $ [_ \ n] || (syms, NAT_REC (HOLE, zer, (x,y, succ)) :: stk) =>
       let
         val rho = Var.Ctx.insert (Var.Ctx.singleton x n) y @@ Syn.into @@ Syn.NAT_REC (n, (zer, (x,y,succ)))
       in
         CRITICAL @@ substVarenv rho succ || (syms, stk)
       end
     | O.MONO O.NAT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.MONO O.NAT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.MONO O.INT $ _ || (_, []) => raise Final
     | O.MONO O.NEGSUCC $ _ || (_, []) => raise Final
     | O.MONO O.INT_REC $ [_ \ m, (_,[x,y]) \ p, _ \ q, (_,[x',y']) \ r] || (syms, stk) => COMPAT @@ m || (syms, INT_REC (HOLE, (x,y,p), q, (x',y',r)) :: stk) 
     | O.MONO O.ZERO $ _ || (syms, INT_REC (HOLE, _, q, _) :: stk) => CRITICAL @@ q || (syms, stk)
     | O.MONO O.SUCC $ [_ \ n] || (syms, INT_REC (HOLE, (x,y,p), zer, (x',y',q)) :: stk) => 
       let
         val rho = Var.Ctx.insert (Var.Ctx.singleton x' n) y' @@ Syn.into @@ Syn.INT_REC (n, ((x,y,p), zer, (x',y',q)))
       in
         CRITICAL @@ substVarenv rho q || (syms, stk)
       end
     | O.MONO O.NEGSUCC $ [_ \ n] || (syms, INT_REC (HOLE, (x,y,p), zer, (x',y',q)) :: stk) => 
       let
         val rho = Var.Ctx.insert (Var.Ctx.singleton x n) y @@ Syn.into @@ Syn.INT_REC (n, ((x,y,p), zer, (x',y',q)))
       in
         CRITICAL @@ substVarenv rho p || (syms, stk)
       end
     | O.MONO O.INT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.MONO O.INT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.MONO O.AX $ _ || (_, []) => raise Final
     | O.MONO O.VOID $ _ || (_, []) => raise Final

     | O.MONO O.WBOOL $ _ || (_, []) => raise Final
     | O.MONO O.BOOL $ _ || (_, []) => raise Final
     | O.MONO O.TT $ _ || (_, []) => raise Final
     | O.MONO O.FF $ _ || (_, []) => raise Final

     | O.MONO O.IF $ [_ \ m, _ \ t, _ \ f] || (syms, stk) => COMPAT @@ m || (syms, IF (HOLE, t, f) :: stk)
     | O.MONO O.WIF $ [(_,[x]) \ tyx, _ \ m, _ \ t, _ \ f] || (syms, stk) => COMPAT @@ m || (syms, WIF ((x, tyx), HOLE, t, f) :: stk)
     | O.MONO O.TT $ _ || (syms, IF (HOLE, t, _) :: stk) => CRITICAL @@ t || (syms, stk)
     | O.MONO O.TT $ _ || (syms, WIF (_, HOLE, t, _) :: stk) => CRITICAL @@ t || (syms, stk)
     | O.MONO O.FF $ _ || (syms, IF (HOLE, _, f) :: stk) => CRITICAL @@ f || (syms, stk)
     | O.MONO O.FF $ _ || (syms, WIF (_, HOLE, _, f) :: stk) => CRITICAL @@ f || (syms, stk)
     | O.MONO O.BOOL $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.MONO O.BOOL $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)
     | O.MONO O.WBOOL $ _ || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val fcom =
           Syn.into @@ Syn.FCOM
             {dir = dir,
              cap = cap,
              tubes = tubes}
       in
         CRITICAL @@ fcom || (syms, stk)
       end
     | O.MONO O.WBOOL $ _ || (syms, COE (_, (u, HOLE), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.MONO O.S1 $ _ || (_, []) => raise Final
     | O.MONO O.BASE $ _ || (_, []) => raise Final
     | O.POLY (O.LOOP r) $ _ || (syms, stk) =>
       (case r of 
           P.APP P.DIM0 => STEP @@ Syn.into Syn.BASE || (syms, stk)
         | P.APP P.DIM1 => STEP @@ Syn.into Syn.BASE || (syms, stk)
         | P.VAR u => 
             if stability = CUBICAL andalso not (SymSet.member syms u) then raise Unstable else
              case stk of 
                 [] => raise Final
               | S1_REC (_, HOLE, _, (v, loop)) :: stk => CRITICAL @@ substSymbol (P.ret u, v) loop || (syms, stk)
               | _ => raise Stuck)
     | O.MONO O.BASE $ _ || (syms, S1_REC (_, HOLE, base, _) :: stk) => CRITICAL @@ base || (syms, stk)
     | O.MONO O.S1 $ _ || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val fcom =
           Syn.into @@ Syn.FCOM
             {dir = dir,
              cap = cap,
              tubes = tubes}
       in
         CRITICAL @@ fcom || (syms, stk)
       end
     | O.MONO O.S1 $ _ || (syms, COE (_, (u, HOLE), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.MONO (O.RECORD _) $ _ || (_, []) => raise Final
     | O.MONO (O.TUPLE _) $ _ || (_, []) => raise Final
     | O.MONO (O.PROJ lbl) $ [_ \ m] || (syms, stk) => COMPAT @@ m || (syms, PROJ (lbl, HOLE) :: stk)
     | O.MONO (O.TUPLE_UPDATE lbl) $ [_ \ n, _ \ m] || (syms, stk) => COMPAT @@ m || (syms, TUPLE_UPDATE (lbl, n, HOLE) :: stk)
     | O.MONO (O.TUPLE lbls) $ args || (syms, PROJ (lbl, HOLE) :: stk) =>
       let
         val dict = Syn.outTupleFields (lbls, args)
       in
         CRITICAL @@ Syn.LabelDict.lookup dict lbl || (syms, stk)
         handle Syn.LabelDict.Absent => raise Stuck
       end
     | O.MONO (O.TUPLE lbls) $ args || (syms, TUPLE_UPDATE (lbl, n, HOLE) :: stk) =>
       let
         val dict = Syn.outTupleFields (lbls, args)
         val (lbls', args') = Syn.intoTupleFields @@ Syn.LabelDict.insert dict lbl n
       in
         CRITICAL @@ O.MONO (O.TUPLE lbls') $$ args' || (syms, stk)
       end
     | O.MONO (O.RECORD lbls) $ args || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) => 
       (case (lbls, args) of 
           ([], []) =>
           let
             val tuple = Syn.into @@ Syn.TUPLE @@ Syn.LabelDict.empty
           in
             CRITICAL @@ tuple || (syms, stk)
           end
         | (lbl :: lbls, ([],[]) \ ty :: args) =>
           let
             val (r, r') = dir
             fun proj m = Syn.into @@ Syn.PROJ (lbl, m)
             fun head s =
               Syn.into @@ Syn.HCOM
                 {dir = (r, s),
                  ty = ty,
                  cap = proj cap,
                  tubes = mapTubes_ proj tubes}

             fun shiftField s = 
               fn ([], x :: xs) \ ty => ([], xs) \ substVar (head s, x) ty
                | _ => raise Fail "Impossible field"

             val u = Sym.named "u"
             val ty'u = O.MONO (O.RECORD lbls) $$ List.map (shiftField (P.ret u)) args

             val tail =
               Syn.into @@ Syn.COM
                 {dir = dir,
                  ty = (u, ty'u),
                  cap = cap,
                  tubes = tubes}
           in
             CRITICAL @@ tail || (syms, TUPLE_UPDATE (lbl, head r', HOLE) :: stk)
           end
         | _ => raise Fail "Impossible record type")
     (* | O.MONO (O.RECORD lbls) $ tys || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         fun wrap m = ([],[]) \ m
         fun hcom (lbl, _ \ ty) =
           wrap o Syn.into @@ Syn.HCOM 
             {dir = dir,
              ty = ty,
              cap = Syn.into @@ Syn.PROJ (lbl, cap),
              tubes = mapTubes_ (fn n => Syn.into @@ Syn.PROJ (lbl, n)) tubes}
         val tuple = O.MONO (O.TUPLE lbls) $$ ListPair.mapEq hcom (lbls, tys)
       in
         CRITICAL @@ tuple || (syms, stk)
       end *)
     (* | O.MONO (O.RECORD lbls) $ tys || (syms, COE (dir, (u, HOLE), coercee) :: stk) => 
       let
         fun wrap m = ([],[]) \ m
         fun coe (lbl, _ \ ty) = 
           wrap o Syn.into @@ Syn.COE 
             {dir = dir,
              ty = (u, ty),
              coercee = Syn.into @@ Syn.PROJ (lbl, coercee)}
         val tuple = O.MONO (O.TUPLE lbls) $$ ListPair.mapEq coe (lbls, tys)
       in
         CRITICAL @@ tuple || (SymSet.remove syms u, stk)
       end *)

     (* forms of judgment *)
     | O.MONO O.JDG_EQ $ _ || (_, []) => raise Final
     | O.MONO O.JDG_EQ_TYPE $ _ || (_, []) => raise Final
     | O.MONO O.JDG_TRUE $ _ || (_, []) => raise Final
     | O.MONO O.JDG_SYNTH $ _ || (_, []) => raise Final
     | O.MONO O.JDG_DIM_SUBST $ _ || (_, []) => raise Final
     | O.MONO (O.JDG_TERM _) $ _ || (_, []) => raise Final

     (* rules, tactics and multitactics *)
     | O.MONO O.MTAC_ALL $ _ || (_, []) => raise Final
     | O.MONO (O.MTAC_EACH _) $ _ || (_, []) => raise Final
     | O.MONO (O.MTAC_FOCUS _) $ _ || (_, []) => raise Final
     | O.MONO (O.MTAC_SEQ _) $ _ || (_, []) => raise Final
     | O.MONO O.MTAC_ORELSE $ _ || (_, []) => raise Final
     | O.MONO O.MTAC_REC $ _ || (_, []) => raise Final
     | O.MONO (O.MTAC_HOLE _) $ _ || (_, []) => raise Final
     | O.MONO O.TAC_MTAC $ _ || (_, []) => raise Final
     | O.MONO O.RULE_ID $ _ || (_, []) => raise Final
     | O.MONO (O.RULE_PRIM _) $ _ || (_, []) => raise Final
     | O.MONO (O.RULE_EXACT _) $ _ || (_, []) => raise Final
     | O.MONO O.RULE_SYMMETRY $ _ || (_, []) => raise Final
     | O.MONO O.RULE_AUTO_STEP $ _ || (_, []) => raise Final
     | O.POLY (O.RULE_HYP _) $ _ || (_, []) => raise Final
     | O.POLY (O.RULE_ELIM _) $ _ || (_, []) => raise Final
     | O.MONO O.RULE_HEAD_EXP $ _ || (_, []) => raise Final
     | O.MONO O.RULE_CUT $ _ || (_, []) => raise Final
     | O.POLY (O.RULE_UNFOLD _) $ _ || (_, []) => raise Final
     | O.POLY (O.RULE_LEMMA _) $ _ || (_, []) => raise Final
     | O.POLY (O.RULE_CUT_LEMMA _) $ _ || (_, []) => raise Final
     | O.MONO O.MTAC_REPEAT $ [_ \ mt] || (syms, stk) => 
       let
         val x = Var.named "x"
         val xtm = check (`x, O.MTAC)
         val mtrec = O.MONO O.MTAC_REC $$ [([],[x]) \ Tac.mtry (Tac.seq (Tac.mprogress mt) [] xtm)]
       in
         STEP @@ mtrec || (syms, stk)
       end
     | O.MONO O.MTAC_AUTO $ _ || (syms, stk) => STEP @@ Tac.multirepeat (Tac.all (Tac.try Tac.autoStep)) || (syms, stk)
     | O.MONO (O.DEV_LET tau) $ [_ \ jdg, _ \ tac1, ([u],_) \ tac2] || (syms, stk) => 
       let
         val catjdg = RedPrlCategoricalJudgment.fromAbt jdg
         val tau = RedPrlCategoricalJudgment.synthesis catjdg
       in
         STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.cut jdg)) [(u, P.HYP tau)] (Tac.each [tac1,tac2])) || (syms, stk)
       end
     | O.MONO O.DEV_DFUN_INTRO $ [([u],_) \ t] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.prim "dfun/intro")) [(u, P.HYP O.EXP)] (Tac.each [t, Tac.autoTac])) || (syms, stk)
     | O.MONO O.DEV_DPROD_INTRO $ [_ \ t1, _ \ t2] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.prim "dpair/intro")) [] (Tac.each [t1, t2, Tac.autoTac])) || (syms, stk)
     | O.MONO O.DEV_PATH_INTRO $ [([u], _) \ t] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.prim "path/intro")) [(u, P.DIM)] (Tac.each [t, Tac.autoTac, Tac.autoTac])) || (syms, stk)
     | O.POLY (O.DEV_BOOL_ELIM z) $ [_ \ t1, _ \ t2] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [] (Tac.each [t1,t2])) || (syms, stk)
     | O.POLY (O.DEV_S1_ELIM z) $ [_ \ t1, ([v],_) \ t2] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(v, P.DIM)] (Tac.each [t1,t2, Tac.autoTac, Tac.autoTac])) || (syms, stk)
     | O.POLY (O.DEV_DFUN_ELIM z) $ [_ \ t1, ([x,p],_) \ t2] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(x, P.HYP O.EXP), (p, P.HYP O.EXP)] (Tac.each [t1,t2])) || (syms, stk)
     | O.POLY (O.DEV_DPROD_ELIM z) $ [([x,y], _) \ t] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(x, P.HYP O.EXP), (y, P.HYP O.EXP)] (Tac.each [t])) || (syms, stk)
     | O.POLY (O.DEV_PATH_ELIM z) $ [_ \ t1, ([x,p],_) \ t2] || (syms, stk) => STEP @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(x, P.HYP O.EXP), (p, P.HYP O.EXP)] (Tac.each [t1, Tac.autoTac, Tac.autoTac, t2])) || (syms, stk)
     | _ => raise Stuck

  fun step sign stability unfolding (tm || stk) =
    let
      val (view, tau) = infer tm
    in
      stepView sign stability unfolding tau (view || stk)
    end

  fun init tm = 
    tm || (SymSet.empty, [])

  datatype canonicity =
     CANONICAL
   | NEUTRAL of blocker
   | REDEX
   | STUCK
   | UNSTABLE


  val unwrapAction = 
    fn COMPAT cfg => cfg
     | STEP cfg => cfg
     | CRITICAL cfg => cfg

  fun eval sign stability unfolding = 
    let
      fun go cfg =
        go (unwrapAction (step sign stability unfolding cfg))
        handle Stuck => cfg
             | Final => cfg
             | Neutral _ => cfg 
             | Unstable => cfg
    in
      unload o go o init
    end

  fun steps sign stability unfolding n = 
    let
      fun go1 cfg = 
        case step sign stability unfolding cfg of 
           COMPAT cfg' => go1 cfg'
         | CRITICAL cfg' => cfg'
         | STEP cfg' => cfg'

      fun go 0 cfg = cfg
        | go n cfg = go (n - 1) (go1 cfg)
    in
      unload o go n o init
    end

  fun canonicity sign stability unfolding tm =
    (steps sign stability unfolding 1 tm; REDEX) 
    handle Stuck => STUCK
         | Final => CANONICAL
         | Unstable => UNSTABLE
         | Neutral blocker => NEUTRAL blocker
end
