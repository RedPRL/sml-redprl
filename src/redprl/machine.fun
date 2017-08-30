functor RedPrlMachine (Sig : MINI_SIGNATURE) : REDPRL_MACHINE =
struct
  structure E = RedPrlError
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
   | WIF of (variable * abt) * hole * abt * abt
   | S1_REC of (variable * abt) * hole * abt * (symbol * abt)
   | IF of hole * abt * abt
   | PATH_APP of hole * symbol P.t
   | NAT_REC of hole * abt * (variable * variable * abt)
   | INT_REC of hole * abt * (variable * variable * abt) * abt * (variable * variable * abt)
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
       | IF (HOLE, t, f) => Syn.into @@ Syn.IF (m, (t, f))
       | WIF ((x, tyx), HOLE, t, f) => Syn.into @@ Syn.WIF ((x, tyx), m, (t, f))
       | S1_REC ((x, tyx), HOLE, base, (u, loop)) => Syn.into @@ Syn.S1_REC ((x, tyx), m, (base, (u, loop)))
       | PATH_APP (HOLE, r) => Syn.into @@ Syn.PATH_APP (m, r)
       | NAT_REC (HOLE, zer, (x, y, succ)) => Syn.into @@ Syn.NAT_REC (m, (zer, (x, y, succ)))
       | INT_REC (HOLE, zer, (x,y,succ), negone, (x',y',negss)) => Syn.into @@ Syn.INT_REC (m, (zer, (x,y,succ), negone, (x',y',negss)))
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
            let
              fun isBound syms r =
                case r of
                   P.VAR x => SymSet.member syms x
                 | P.APP _ => false
              fun isConstant r =
                case r of
                   P.VAR _ => false
                 | P.APP P.DIM0 => true
                 | P.APP P.DIM1 => true
                 | P.APP _ => E.raiseError (E.INVALID_DIMENSION (TermPrinter.ppParam r))
            in
              if isBound syms r1 orelse isBound syms r2 orelse (isConstant r1 andalso isConstant r2) then
                false
              else
                raise Unstable
            end

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
           | HCOM (dir, HOLE, cap, tubes) :: stk =>
               E.raiseError (E.UNIMPLEMENTED (Fpp.text "hcom operations of fcom types"))
           | COE (_, (u, _), coercee) :: stk =>
               E.raiseError (E.UNIMPLEMENTED (Fpp.text "coe operations of fcom types"))
           | _ => raise Stuck)

  fun stepView sign stability unfolding tau =
    fn `x || _ => raise Neutral (VAR x)
     | x $# (rs, ms) || _ => raise Neutral (METAVAR x)

     | O.MONO O.AX $ _ || (_, []) => raise Final

     | O.POLY (O.CUST (opid, ps, _)) $ args || (syms, stk) =>
       if not (unfolding opid) then raise Neutral (OPERATOR opid) else
       let
         val entry as {state, ...} = Sig.lookup sign opid
         val state = state (fn _ => RedPrlSym.new ())
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

     | O.MONO O.EQUALITY $ _ || (_, []) => raise Final
     | O.MONO O.EQUALITY $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.MONO O.EQUALITY $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.MONO O.NAT $ _ || (_, []) => raise Final
     | O.MONO O.ZERO $ _ || (_, []) => raise Final
     | O.MONO O.SUCC $ _ || (_, []) => raise Final
     | O.MONO O.NAT_REC $ [_ \ m, _ \ n, (_,[x,y]) \ p] || (syms, stk) => COMPAT @@ m || (syms, NAT_REC (HOLE, n, (x,y,p)) :: stk)
     | O.MONO O.ZERO $ _ || (syms, NAT_REC (HOLE, zer, _) :: stk) => CRITICAL @@ zer || (syms, stk)
     | O.MONO O.SUCC $ [_ \ n] || (syms, NAT_REC (HOLE, zer, (x,y, succ)) :: stk) =>
       let
         val rho = VarKit.ctxFromList [(n, x), (Syn.into @@ Syn.NAT_REC (n, (zer, (x,y,succ))), y)]
       in
         CRITICAL @@ substVarenv rho succ || (syms, stk)
       end
     | O.MONO O.NAT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.MONO O.NAT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.MONO O.INT $ _ || (_, []) => raise Final
     | O.MONO O.NEGSUCC $ _ || (_, []) => raise Final
     | O.MONO O.INT_REC $ [_ \ m, _ \ n, (_,[x,y]) \ p, _ \ q, (_,[x',y']) \ r] || (syms, stk) => COMPAT @@ m || (syms, INT_REC (HOLE, n, (x,y,p), q, (x',y',r)) :: stk)
     | O.MONO O.ZERO $ _ || (syms, INT_REC (HOLE, n, _, _, _) :: stk) => CRITICAL @@ n || (syms, stk)
     | O.MONO O.SUCC $ [_ \ m] || (syms, INT_REC (HOLE, n, (x,y,p), _, _) :: stk) =>
       let
         val rho = VarKit.ctxFromList [(m, x), (Syn.into @@ Syn.NAT_REC (m, (n, (x,y,p))), y)]
       in
         CRITICAL @@ substVarenv rho p || (syms, stk)
       end
     | O.MONO O.NEGSUCC $ [_ \ m] || (syms, INT_REC (HOLE, _, _, q, (x,y,r)) :: stk) =>
       COMPAT @@ m || (syms, NAT_REC (HOLE, q, (x,y,r)) :: stk)
     | O.MONO O.INT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.MONO O.INT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

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
         | P.APP _ => E.raiseError (E.INVALID_DIMENSION (TermPrinter.ppParam r))
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
         val fields = Syn.outTupleFields (lbls, args)
       in
         CRITICAL @@ Syn.Fields.lookup lbl fields || (syms, stk)
         handle Syn.Fields.Absent => raise Stuck
       end
     | O.MONO (O.TUPLE lbls) $ args || (syms, TUPLE_UPDATE (lbl, n, HOLE) :: stk) =>
       let
         val fields = Syn.outTupleFields (lbls, args)
         val (lbls', args') = Syn.intoTupleFields @@ Syn.Fields.update (lbl, n) fields
       in
         CRITICAL @@ O.MONO (O.TUPLE lbls') $$ args' || (syms, stk)
       end
     | O.MONO (O.RECORD lbls) $ args || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) => 
       (case (lbls, args) of 
           ([], []) =>
           let
             val tuple = Syn.into @@ Syn.TUPLE Syn.Fields.empty
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
     | O.MONO (O.RECORD lbls) $ args || (syms, COE (dir, (u, HOLE), coercee) :: stk) =>  
       (case (lbls, args) of 
           ([], []) =>
           let
             val tuple = Syn.into @@ Syn.TUPLE Syn.Fields.empty
           in
             CRITICAL @@ tuple || (syms, stk)
           end
         | (lbl :: lbls, ([],[]) \ ty :: args) =>
           let
             val (r, r') = dir
             fun proj m = Syn.into @@ Syn.PROJ (lbl, m)
             fun head s =
               Syn.into @@ Syn.COE
                 {dir = (r, s),
                  ty = (u, ty),
                  coercee = proj coercee}

             fun shiftField s = 
               fn ([], x :: xs) \ ty => ([], xs) \ substVar (head s, x) ty
                | _ => raise Fail "Impossible field"

             val u = Sym.named "u"
             val ty'u = O.MONO (O.RECORD lbls) $$ List.map (shiftField (P.ret u)) args

             val tail =
               Syn.into @@ Syn.COE
                 {dir = dir,
                  ty = (u, ty'u),
                  coercee = coercee}
           in
             CRITICAL @@ tail || (syms, TUPLE_UPDATE (lbl, head r', HOLE) :: stk)
           end
         | _ => raise Fail "Impossible record type")

     | O.POLY (O.UNIVERSE _) $ _ || (_, []) => raise Final
     | O.POLY (O.UNIVERSE _) $ _ || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val fcom =
           Syn.into @@ Syn.FCOM
             {dir = dir,
              cap = cap,
              tubes = tubes}
       in
         CRITICAL @@ fcom || (syms, stk)
       end
     | O.POLY (O.UNIVERSE _) $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

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
