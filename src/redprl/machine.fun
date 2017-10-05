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
  structure P = struct open RedPrlParameterTerm RedPrlSortData end

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


  type tube = Syn.equation * (symbol * abt)
  type boundary = Syn.equation * abt

  datatype hole = HOLE
  datatype frame =
     APP of hole * abt
   | HCOM of Syn.dir * hole * abt * tube list
   | COE of Syn.dir * (symbol * hole) * abt
   | WIF of (variable * abt) * hole * abt * abt
   | S1_REC of (variable * abt) * hole * abt * (symbol * abt)
   | IF of hole * abt * abt
   | PATH_APP of hole * abt
   | NAT_REC of hole * abt * (variable * variable * abt)
   | INT_REC of hole * abt * (variable * variable * abt) * abt * (variable * variable * abt)
   | PROJ of string * hole
   | TUPLE_UPDATE of string * abt * hole
   | CAP of Syn.dir * tube list * hole
   | VPROJ of symbol * hole * abt

  type stack = frame list
  type bound_syms = SymSet.set

  datatype 'a machine = || of 'a * (bound_syms * stack)

  val todo = Fail "TODO"
  fun ?e = raise e

  local
    fun plug m = 
      fn APP (HOLE, n) => Syn.intoApp (m, n)
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
       | CAP (dir, tubes, HOLE) => Syn.into @@ Syn.CAP {dir = dir, tubes = tubes, coercee = m}
       | VPROJ (x, HOLE, f) => Syn.into @@ Syn.VPROJ (VarKit.toDim x, m, f)
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
          _ >> RedPrlAtomicJudgment.TRUE _ => false
        | _ => true
      end

    fun never _ = false
    fun always _ = true
  end

  exception Neutral of blocker
  exception Unstable
  exception Final
  exception Stuck

  local
    fun assertVariable stability syms u =
      case stability of
        NOMINAL => ()
      | CUBICAL =>
          if SymSet.member syms u then ()
          else raise Unstable
  in
    fun branchOnDim stability syms r f0 f1 fu =
      case Syn.out r of
         Syn.DIM0 => f0
       | Syn.DIM1 => f1
       | Syn.VAR (u, _) => (assertVariable stability syms u; fu u)
       | Syn.META (u, _) => (assertVariable stability syms u; fu u)
  end

  fun dimensionsEqual stability syms (r1, r2) = 
    (* If two dimensions are equal, then no substitution can ever change that. *)
    if Tm.eq (r1, r2) then 
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
                case Tm.out r of
                   ` x => SymSet.member syms x
                 | _ => false
              fun isConstant r =
                case Syn.out r of
                   Syn.DIM0 => true
                 | Syn.DIM1 => true
                 | _ => false
            in
              if isBound syms r1 orelse isBound syms r2 orelse (isConstant r1 andalso isConstant r2) then
                false
              else
                raise Unstable
            end

  fun findFirstWithTrueEquation stability syms =
    let
      val rec aux = 
        fn [] => NONE
         | (eq, x) :: xs =>
           if dimensionsEqual stability syms eq then 
             SOME x
           else 
             aux xs
    in
      aux
    end

  fun mapTubes f : tube list -> tube list = List.map (fn (eq, (u, n)) => (eq, (u, f (u, n))))

  fun zipTubesWith f : Syn.equation list * abt bview list -> tube list =
    ListPair.mapEq (fn (eq, ([u], _) \ n) => (eq, (u, f (u, n))))

  fun zipBoundariesWith f : Syn.equation list * abt bview list -> boundary list =
    ListPair.mapEq (fn (eq, _ \ n) => (eq, f n))

  fun mapTubes_ f = mapTubes (f o #2)
  val zipTubes = zipTubesWith #2
  val zipBoundaries = zipBoundariesWith (fn n => n)

  datatype 'a action = 
     COMPAT of 'a
   | CRITICAL of 'a
   | STEP of 'a

  fun stepFCom stability ({dir = dir as (r, r'), cap, tubes} || (syms, stk)) =
    if dimensionsEqual stability syms dir then 
      STEP @@ cap || (syms, stk)
    else
      case findFirstWithTrueEquation stability syms tubes of
         SOME (u, n) => STEP @@ substVar (r', u) n || (syms, stk)
       | NONE =>
         (case stk of
             [] => raise Final
           | WIF ((x, tyx), HOLE, t, f) :: stk =>
             let
               val u = Sym.named "u"
               val fcomu =
                 Syn.into @@ Syn.FCOM
                   {dir = (r, VarKit.toDim u),
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
                   {dir = (r, VarKit.toDim u),
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
           | HCOM _ :: stk =>
               E.raiseError (E.UNIMPLEMENTED (Fpp.text "hcom operations of fcom types"))
           | COE _ :: stk =>
               E.raiseError (E.UNIMPLEMENTED (Fpp.text "coe operations of fcom types"))
           | _ => raise Stuck)

  fun stepBox stability ({dir, cap, boundaries} || (syms, stk)) =
    if dimensionsEqual stability syms dir then
      STEP @@ cap || (syms, stk)
    else
      case findFirstWithTrueEquation stability syms boundaries of
         SOME b => STEP @@ b || (syms, stk)
       | NONE =>
         (case stk of
             [] => raise Final
           | CAP _ :: stk =>
               STEP @@ cap || (syms, stk)
           | _ => raise Stuck)

  fun stepCap stability ({dir as (r, r'), tubes, coercee} || (syms, stk)) =
    if dimensionsEqual stability syms dir then
      STEP @@ coercee || (syms, stk)
    else
      case findFirstWithTrueEquation stability syms tubes of
         SOME (u, a) => STEP @@ (Syn.into @@ Syn.COE {dir = (r', r), ty = (u, a), coercee = coercee}) || (syms, stk)
       | NONE => COMPAT @@ coercee || (syms, CAP (dir, tubes, HOLE) :: stk)

  fun stepView sign stability unfolding tau =
    fn `x || _ => raise Neutral (VAR x)
     | x $# (rs, ms) || _ => raise Neutral (METAVAR x)

     | O.MONO O.AX $ _ || (_, []) => raise Final

     | O.POLY (O.CUST (opid, _)) $ args || (syms, stk) =>
       if not (unfolding opid) then raise Neutral (OPERATOR opid) else
       let
         val entry as {state, ...} = Sig.lookup sign opid
         val Lcf.|> (psi, evd) = state (fn _ => Sym.named "?")
         val state = state (fn _ => RedPrlSym.new ())
         val term = Sig.unfoldCustomOperator entry args
       in
         STEP @@ term || (syms, stk)
       end  

     | O.MONO O.HCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ system] || (syms, stk) => COMPAT @@ ty || (syms, HCOM ((r1, r2), HOLE, cap, Syn.outTubes system) :: stk)
     | O.MONO O.COE $ [_ \ r1, _ \ r2, (_, [u]) \ ty, _ \ coercee] || (syms, stk) => COMPAT @@ ty || (SymSet.insert syms u, COE ((r1,r2), (u, HOLE), coercee) :: stk)
     | O.MONO O.COM $ [_ \ r, _ \ r', (_, [u]) \ ty, _ \ cap, _ \ system] || (syms, stk) =>
       let
         fun coe s m = 
           Syn.into @@ Syn.COE
             {dir = (s, r'),
              ty = (u, ty),
              coercee = m}
          val hcom =
            Syn.into @@ Syn.HCOM
              {dir = (r, r'),
               ty = substVar (r', u) ty,
               cap = coe r cap,
               tubes = List.map (fn ((r1, r2), (u, n)) => ((r1, r2), (u, coe (VarKit.toDim u) n))) (Syn.outTubes system)}
       in
         STEP @@ hcom || (syms, stk)
       end

     | O.MONO O.FCOM $ [_ \ r1, _ \ r2, _ \ cap, _ \ tubes] || (syms, stk) => 
       stepFCom stability ({dir = (r1,r2), cap = cap, tubes = Syn.outTubes tubes} || (syms, stk))

     | O.MONO O.LAM $ _ || (_, []) => raise Final
     | O.MONO O.FUN $ _ || (_, []) => raise Final

     | O.MONO O.APP $ [_ \ m, _ \ n] || (syms, stk) => COMPAT @@ m || (syms, APP (HOLE, n) :: stk)
     | O.MONO O.LAM $ [(_,[x]) \ m] || (syms, APP (HOLE, n) :: stk) => CRITICAL @@ substVar (n, x) m || (syms, stk)
     | O.MONO O.FUN $ [_ \ tyA, (_,[x]) \ tyBx] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val xtm = VarKit.toExp x
         fun apx n = Syn.intoApp (n, xtm)
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
     | O.MONO O.FUN $ [_ \ tyA, (_,[x]) \ tyBx] || (syms, COE (dir, (u, HOLE), coercee) :: stk) =>
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
                 ty = (u, substVar (xcoe (VarKit.toDim u), x) tyBx),
                 coercee = Syn.intoApp (coercee, xcoe r)})
       in
         CRITICAL @@ lambda || (SymSet.remove syms u, stk)
       end

     | O.MONO O.PATH_ABS $ _ || (_, []) => raise Final
     | O.MONO O.PATH_TY $ _ || (_, []) => raise Final

     | O.MONO O.PATH_APP $ [_ \ m, _ \ r] || (syms, stk) => COMPAT @@ m || (syms, PATH_APP (HOLE, r) :: stk)
     | O.MONO O.PATH_ABS $ [(_, [x]) \ m] || (syms, PATH_APP (HOLE, r) :: stk) => CRITICAL @@ substVar (r, x) m || (syms, stk)

     | O.MONO O.PATH_TY $ [(_, [u]) \ tyu, _ \ m0, _ \ m1] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         fun apu m = Syn.into @@ Syn.PATH_APP (m, check (`u, O.DIM))
         val v = Sym.named "_"
         val hcomu =
           Syn.into @@ Syn.HCOM
             {dir = dir,
              ty = tyu,
              cap = apu cap,
              tubes = ((VarKit.toDim u, Syn.into Syn.DIM0), (v, m0)) :: ((VarKit.toDim u, Syn.into Syn.DIM1), (v, m1)) :: mapTubes_ apu tubes}
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
              cap = Syn.into @@ Syn.PATH_APP (coercee, check (`u, O.DIM)),
              tubes = [((VarKit.toDim u, Syn.into Syn.DIM0), (v, m0v)), ((VarKit.toDim u, Syn.into Syn.DIM1), (v, m1v))]}
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
     | O.MONO O.LOOP $ [_ \ r] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ Syn.into Syn.BASE || (syms, stk))
           (STEP @@ Syn.into Syn.BASE || (syms, stk))
           (fn u =>
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
             val ty'u = O.MONO (O.RECORD lbls) $$ List.map (shiftField (VarKit.toDim u)) args

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
             val ty'u = O.MONO (O.RECORD lbls) $$ List.map (shiftField (VarKit.toDim u)) args

             val tail =
               Syn.into @@ Syn.COE
                 {dir = dir,
                  ty = (u, ty'u),
                  coercee = coercee}
           in
             CRITICAL @@ tail || (syms, TUPLE_UPDATE (lbl, head r', HOLE) :: stk)
           end
         | _ => raise Fail "Impossible record type")

     | O.MONO O.BOX $ [_ \ r1, _ \ r2, _ \ cap, _ \ boundaries] || (syms, stk) => 
       stepBox stability ({dir = (r1, r2), cap = cap, boundaries = Syn.outBoundaries boundaries} || (syms, stk))
     | O.MONO O.CAP $ [_ \ r1, _ \ r2, _ \ coercee, _ \ tubes] || (syms, stk) => 
       stepCap stability ({dir = (r1, r2), coercee = coercee, tubes = Syn.outTubes tubes} || (syms, stk))

     | O.MONO O.V $ [_ \ r, _ \ a, _ \ b, _] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ a || (syms, stk))
           (STEP @@ b || (syms, stk))
           (fn u =>
             case stk of
               [] => raise Final
             | HCOM _ :: stk => E.raiseError (E.UNIMPLEMENTED (Fpp.text "hcom operations of ua types"))
             | COE _ :: stk => E.raiseError (E.UNIMPLEMENTED (Fpp.text "coe operations of ua types"))
             | _ => raise Stuck)
     | O.MONO O.VIN $ [_ \ r, _ \ m, _ \ n] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ m || (syms, stk))
           (STEP @@ n || (syms, stk))
           (fn u =>
             case stk of
               [] => raise Final
             | VPROJ (v, HOLE, f) :: stk =>
                 (* the following line should be equivalent to direct comparison
                  * due to the invariants of the machine, but it does not hurt
                  * much (I hope) to check stability again. *)
                 if dimensionsEqual stability syms (r, VarKit.toDim v) then
                   CRITICAL @@ n || (syms, stk)
                 else
                   raise Stuck
             | _ => raise Stuck)
     | O.MONO O.VPROJ $ [_ \ r, _ \ m, _ \ f] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ Syn.intoApp (f, m) || (syms, stk))
           (STEP @@ m || (syms, stk))
           (fn u => COMPAT @@ m || (syms, VPROJ (u, HOLE, f) :: stk))

     | O.MONO O.UNIVERSE $ _ || (_, []) => raise Final
     | O.MONO O.UNIVERSE $ _ || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val fcom =
           Syn.into @@ Syn.FCOM
             {dir = dir,
              cap = cap,
              tubes = tubes}
       in
         CRITICAL @@ fcom || (syms, stk)
       end
     | O.MONO O.UNIVERSE $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

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
