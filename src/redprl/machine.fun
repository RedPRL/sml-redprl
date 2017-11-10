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
  structure K = RedPrlKind

  type tube = Syn.equation * (variable * abt)
  type boundary = Syn.equation * abt

  datatype hole = HOLE
  datatype frame =
     APP of hole * abt
   | HCOM of Syn.dir * hole * abt * tube list
   | COE of Syn.dir * (variable * hole) * abt
   | WIF of (variable * abt) * hole * abt * abt
   | S1_REC of (variable * abt) * hole * abt * (variable * abt)
   | IF of hole * abt * abt
   | PATH_APP of hole * abt
   | NAT_REC of hole * abt * (variable * variable * abt)
   | INT_REC of hole * abt * (variable * variable * abt) * abt * (variable * variable * abt)
   | PROJ of string * hole
   | TUPLE_UPDATE of string * abt * hole
   | CAP of Syn.dir * tube list * hole
   | VPROJ of variable * hole * abt

  type stack = frame list
  type bound_syms = SymSet.set

  datatype 'a machine = || of 'a * (bound_syms * stack)

  val todo = Fail "TODO"
  fun ?e = raise e

  local
    fun plug m = 
      fn APP (HOLE, n) => Syn.intoApp (m, n)
       | HCOM (dir, HOLE, cap, tubes) => Syn.intoHcom {dir = dir, ty = m, cap = cap, tubes = tubes}
       | COE (dir, (u, HOLE), coercee) => Syn.intoCoe {dir = dir, ty = (u, m), coercee = coercee}
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
     STABLE
   | NOMINAL

  datatype blocker =
     VAR of RedPrlAbt.variable
   | METAVAR of RedPrlAbt.metavariable
   | OPERATOR of Sig.opid

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
      | STABLE =>
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
        | STABLE =>
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

  fun mapTubes f : tube list -> tube list = List.map (fn (eq, (u, n)) => (eq, f (u, n)))
  fun mapTubes_ f = mapTubes (fn (v, tm) => (v, f tm))

  fun zipTubesWith f : Syn.equation list * abt bview list -> tube list =
    ListPair.mapEq (fn (eq, [u] \ n) => (eq, (u, f (u, n))))

  fun zipBoundariesWith f : Syn.equation list * abt bview list -> boundary list =
    ListPair.mapEq (fn (eq, _ \ n) => (eq, f n))

  val zipTubes = zipTubesWith #2
  val zipBoundaries = zipBoundariesWith (fn n => n)

  (* assuming u is bound and so the comparison is stable,
   * which is the case in its usage (Kan operations of fcom). *)
  fun keepApartTubes u : tube list -> tube list =
    let
      fun apart r = branchOnDim NOMINAL SymSet.empty r true true (fn v => not (Sym.eq (u, v)))
    in
      List.filter (fn ((r1, r2), _) => apart r1 andalso apart r2)
    end

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
                 Syn.intoFcom
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
                 Syn.intoFcom
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
           | HCOM (hcomDir, HOLE, hcomCap, hcomTubes) :: stk =>
               (* favonia: the version implemented below is different from the one
                *          in CHTT Part III. I do not know which one is better. *)
               let
                 val fcomDir = dir
                 val fcomTubes = tubes
                 val a = cap
                 val dir = () (* prevents any ambiguous usage *)
                 val tubes = () (* prevents any ambiguous usage *)
                 val cap = () (* prevents any ambiguous usage *)
                 fun capOf x = Syn.into @@ Syn.CAP
                   {dir = fcomDir, coercee = x, tubes = fcomTubes}
                 (* within a tube face, the cap operator is simplified: *)
                 fun capOfInTube (v, b) x = Syn.intoCoe
                   {dir = (#2 fcomDir, #1 fcomDir),
                    ty = (v, b),
                    coercee = x}
                 fun hcomCoe (v, b) dest = Syn.intoHcom
                   {dir = (#1 hcomDir, dest),
                    ty = a,
                    cap = capOfInTube (v, b) hcomCap,
                    tubes = mapTubes_ (capOfInTube (v, b)) hcomTubes
                    (* here the bound variable is reused *)}
                 fun coeHcom (v, b) dest = capOfInTube (v, b) @@ Syn.intoHcom
                   {dir = (#1 hcomDir, dest),
                    ty = substVar (#2 fcomDir, v) b,
                    cap = hcomCap,
                    tubes = hcomTubes}
                 fun recovery (v, b) recoverDim =
                   let
                     val y = Sym.named "y"
                   in
                     Syn.intoHcom
                       {dir = hcomDir,
                        ty = a,
                        cap = capOfInTube (v, b) hcomCap,
                        tubes =
                          ((recoverDim, #1 fcomDir), (y, hcomCoe (v, b) (VarKit.toDim y)))
                          ::
                          ((recoverDim, #2 fcomDir), (y, coeHcom (v, b) (VarKit.toDim y)))
                          ::
                          mapTubes_ (capOfInTube (v, b)) hcomTubes}
                   end
                 val recovered =
                   let
                     val dummy = Sym.named "_"
                   in
                     Syn.intoHcom
                       {dir = fcomDir,
                        ty = a,
                        cap = Syn.intoHcom
                          {dir = hcomDir,
                           ty = a,
                           cap = capOf hcomCap,
                           tubes = mapTubes_ capOf hcomTubes},
                        tubes =
                          ((#1 hcomDir, #2 hcomDir), (dummy, capOf hcomCap))
                          ::
                          mapTubes (fn (y, tm) => (dummy, substVar (#2 hcomDir, y) tm)) hcomTubes
                          @
                          mapTubes (fn (v, b) => (v, recovery (v, b) (VarKit.toDim v))) fcomTubes}
                   end
                 val result = Syn.into @@ Syn.BOX
                   {dir = fcomDir,
                    cap = recovered,
                    boundaries = List.map (fn (eq, (v, b)) => (eq, coeHcom (v, b) (#2 hcomDir))) hcomTubes}
               in
                 CRITICAL @@ result || (syms, stk)
               end
           | COE (coeDir, (u, HOLE), coercee) :: stk =>
               let
                 val fcomDir = dir
                 val a = cap
                 val dir = () (* prevents any ambiguous usage of `dir` *)
                 val cap = () (* prevents any ambiguous usage of `cap` *)
                 (* the `origin` handles the case where the coercion should be
                  * the identity function *)
                 fun origin z = substVar (#1 coeDir, u) @@
                   (* note: the above substitution is different from paper in that
                    * it applies to `z` as well, and this is exactly what we want. *)
                   Syn.intoHcom
                     {dir = (#2 fcomDir, z), ty = a,
                      cap = Syn.into @@ Syn.CAP {dir = fcomDir, coercee = coercee, tubes = tubes},
                      tubes = mapTubes
                        (fn (v, b) =>
                          (v, Syn.intoCoe
                            {dir = (VarKit.toDim v, #1 fcomDir),
                             ty = (v, b),
                             coercee = Syn.intoCoe
                               {dir = (#2 fcomDir, VarKit.toDim v),
                                ty = (v, b),
                                coercee = coercee}}))
                        tubes}
                 (* this is the coerced term *)
                 val naivelyCoercedCap = Syn.intoGcom
                   {dir = fcomDir, ty = (u, a),
                    cap = origin (#1 fcomDir),
                    tubes =
                      keepApartTubes u
                        [((#1 fcomDir, #2 fcomDir),
                          (u, Syn.intoCoe
                            {dir = (#1 coeDir, VarKit.toDim u),
                             ty = (u, a),
                             coercee = coercee}))]
                      @
                      mapTubes
                        (fn (v, b) =>
                          (u, Syn.intoCoe
                            {dir = (#2 fcomDir, #1 fcomDir),
                             ty = (v, b),
                             coercee = Syn.intoCoe
                               {dir = (#1 coeDir, VarKit.toDim u),
                                ty = (u, substVar (#2 fcomDir, v) b),
                                coercee = coercee}}))
                        (keepApartTubes u tubes)}
                 fun recovery (v, b) dest =
                   let
                     val coeDestSubst = substVar (#2 coeDir, u)
                   in
                     Syn.intoGcom
                       {dir = (coeDestSubst (#1 fcomDir), dest),
                        ty = (v, coeDestSubst b),
                        cap = naivelyCoercedCap,
                        tubes =
                             ((#1 coeDir, #2 coeDir),
                              (v, Syn.intoCoe
                                {dir = (coeDestSubst (#2 fcomDir), VarKit.toDim v),
                                 ty = (v, coeDestSubst b),
                                 coercee = coercee}))
                          :: mapTubes
                            (fn (v, b) =>
                              (v, Syn.intoCoe
                                {dir = (#2 fcomDir, VarKit.toDim v),
                                 ty = (v, b),
                                 coercee = Syn.intoCoe
                                   {dir = coeDir,
                                    ty = (u, substVar (#2 fcomDir, v) b),
                                    coercee = coercee}}))
                            (keepApartTubes u tubes)}
                   end
                 val coercedCap =
                   let
                     val w = Sym.named "w"
                   in
                     Syn.intoHcom
                       {dir = fcomDir,
                        ty = a,
                        cap = naivelyCoercedCap,
                        tubes =
                          ((#1 coeDir, #2 coeDir),(w, origin (VarKit.toDim w)))
                          ::
                          mapTubes
                            (fn (v, b) =>
                              (w, Syn.intoCoe
                                {dir = (VarKit.toDim w, #2 fcomDir),
                                   ty = (v, b),
                                   coercee = recovery (v, b) (VarKit.toDim w)}))
                          tubes}
                   end
                 val result =
                     substVar (#2 coeDir, u) @@ Syn.into @@ Syn.BOX
                       {dir = fcomDir,
                        cap = coercedCap,
                        boundaries = List.map
                          (fn (eq, (v, b)) =>
                            (eq, recovery (v, b) (#2 fcomDir)))
                          tubes}
               in
                 CRITICAL @@ result || (SymSet.remove syms u, stk)
               end
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
               CRITICAL @@ cap || (syms, stk)
           | _ => raise Stuck)

  fun stepCap stability ({dir as (r, r'), tubes, coercee} || (syms, stk)) =
    if dimensionsEqual stability syms dir then
      STEP @@ coercee || (syms, stk)
    else
      case findFirstWithTrueEquation stability syms tubes of
         SOME (u, a) => STEP @@ (Syn.intoCoe {dir = (r', r), ty = (u, a), coercee = coercee}) || (syms, stk)
       | NONE => COMPAT @@ coercee || (syms, CAP (dir, tubes, HOLE) :: stk)

  fun stepView sign stability unfolding tau =
    fn `x || _ => raise Neutral (VAR x)
     | x $# _ || _ => raise Neutral (METAVAR x)

     | O.AX $ _ || (_, []) => raise Final

     | O.CUST (opid, _) $ args || (syms, stk) =>
       if not (unfolding opid) then raise Neutral (OPERATOR opid) else
       let
         val entry as {state, ...} = Sig.lookup sign opid
         val Lcf.|> (psi, evd) = state (fn _ => Sym.named "?")
         val state = state (fn _ => RedPrlSym.new ())
         val term = Sig.unfoldCustomOperator entry args
       in
         STEP @@ term || (syms, stk)
       end  

     | O.HCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ system] || (syms, stk) => COMPAT @@ ty || (syms, HCOM ((r1, r2), HOLE, cap, Syn.outTubes system) :: stk)
     | O.GHCOM $ [_ \ r1, _ \ r2, _ \ ty, _ \ cap, _ \ system] || (syms, stk) =>
         (case Syn.outTubes system of
            [] => STEP @@ cap || (syms, stk)
          | (tube as (eq, (y, tm))) :: tubes =>
              let
                fun hcom x eps =
                  Syn.intoHcom
                    {dir = (r1, VarKit.toDim x),
                     ty = ty,
                     cap = cap,
                     tubes =
                          ((#2 eq, Syn.intoDim eps), (y, tm))
                       :: ((#2 eq, Syn.intoDim (1 - eps)),
                           (y, Syn.intoGhcom
                             {dir = (r1, VarKit.toDim y),
                              ty = ty,
                              cap = cap,
                              tubes = tubes}))
                       :: tubes}
                val result =
                  Syn.intoHcom
                    {dir = (r1, r2),
                     cap = cap,
                     ty = ty,
                     tubes =
                          ((#1 eq, Syn.intoDim 0), (y, hcom y 0))
                       :: ((#1 eq, Syn.intoDim 1), (y, hcom y 1))
                       :: tube
                       :: tubes}
              in
                STEP @@ result || (syms, stk)
              end)
     | O.COE $ [_ \ r1, _ \ r2, [u] \ ty, _ \ coercee] || (syms, stk) => COMPAT @@ ty || (SymSet.insert syms u, COE ((r1,r2), (u, HOLE), coercee) :: stk)
     | O.COM $ [_ \ r, _ \ r', [u] \ ty, _ \ cap, _ \ system] || (syms, stk) =>
       let
         fun coe s m = 
           Syn.intoCoe
             {dir = (s, r'),
              ty = (u, ty),
              coercee = m}
          val hcom =
            Syn.intoHcom
              {dir = (r, r'),
               ty = substVar (r', u) ty,
               cap = coe r cap,
               tubes = List.map (fn ((r1, r2), (u, n)) => ((r1, r2), (u, coe (VarKit.toDim u) n))) (Syn.outTubes system)}
       in
         STEP @@ hcom || (syms, stk)
       end
     | O.GCOM $ [_ \ r, _ \ r', [u] \ ty, _ \ cap, _ \ system] || (syms, stk) =>
       let
         fun coe s m =
           Syn.intoCoe
             {dir = (s, r'),
              ty = (u, ty),
              coercee = m}
          val ghcom =
            Syn.intoGhcom
              {dir = (r, r'),
               ty = substVar (r', u) ty,
               cap = coe r cap,
               tubes = List.map (fn ((r1, r2), (u, n)) => ((r1, r2), (u, coe (VarKit.toDim u) n))) (Syn.outTubes system)}
       in
         STEP @@ ghcom || (syms, stk)
       end

     | O.FCOM $ [_ \ r1, _ \ r2, _ \ cap, _ \ tubes] || (syms, stk) => 
       stepFCom stability ({dir = (r1,r2), cap = cap, tubes = Syn.outTubes tubes} || (syms, stk))

     | O.LAM $ _ || (_, []) => raise Final
     | O.FUN $ _ || (_, []) => raise Final

     | O.APP $ [_ \ m, _ \ n] || (syms, stk) => COMPAT @@ m || (syms, APP (HOLE, n) :: stk)
     | O.LAM $ [[x] \ m] || (syms, APP (HOLE, n) :: stk) => CRITICAL @@ substVar (n, x) m || (syms, stk)
     | O.FUN $ [_ \ tyA, [x] \ tyBx] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val xtm = VarKit.toExp x
         fun apx n = Syn.intoApp (n, xtm)
         val hcomx =
           Syn.intoHcom
             {dir = dir,
              ty = tyBx,
              cap = apx cap,
              tubes = mapTubes_ apx tubes}
         val lambda = Syn.into @@ Syn.LAM (x, hcomx)
       in
         CRITICAL @@ lambda || (syms, stk)
       end
     | O.FUN $ [_ \ tyA, [x] \ tyBx] || (syms, COE (dir, (u, HOLE), coercee) :: stk) =>
       let
         val (r, r') = dir
         val xtm = Syn.into @@ Syn.VAR (x, O.EXP)
         fun xcoe s =
           Syn.intoCoe
             {dir = (r', s),
              ty = (u, tyA),
              coercee = xtm}
          val lambda =
            Syn.into @@ Syn.LAM (x,
              Syn.intoCoe
                {dir = dir,
                 ty = (u, substVar (xcoe (VarKit.toDim u), x) tyBx),
                 coercee = Syn.intoApp (coercee, xcoe r)})
       in
         CRITICAL @@ lambda || (SymSet.remove syms u, stk)
       end

     | O.PATH_ABS $ _ || (_, []) => raise Final
     | O.PATH_TY $ _ || (_, []) => raise Final
     | O.LINE_TY $ _ || (_, []) => raise Final

     | O.PATH_APP $ [_ \ m, _ \ r] || (syms, stk) => COMPAT @@ m || (syms, PATH_APP (HOLE, r) :: stk)
     | O.PATH_ABS $ [[x] \ m] || (syms, PATH_APP (HOLE, r) :: stk) => CRITICAL @@ substVar (r, x) m || (syms, stk)

     | O.PATH_TY $ [[u] \ tyu, _ \ m0, _ \ m1] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         fun apu m = Syn.into @@ Syn.PATH_APP (m, check (`u, O.DIM))
         val v = Sym.named "_"
         val hcomu =
           Syn.intoHcom
             {dir = dir,
              ty = tyu,
              cap = apu cap,
              tubes = ((VarKit.toDim u, Syn.into Syn.DIM0), (v, m0)) :: ((VarKit.toDim u, Syn.into Syn.DIM1), (v, m1)) :: mapTubes_ apu tubes}
         val abs = Syn.into @@ Syn.PATH_ABS (u, hcomu)
       in
         CRITICAL @@ abs || (syms, stk)
       end
     | O.PATH_TY $ [[u] \ tyuv, _ \ m0v, _ \ m1v] || (syms, COE (dir, (v, HOLE), coercee) :: stk) =>
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

     | O.LINE_TY $ [[u] \ tyu] || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) => ?todo
     | O.LINE_TY $ [[u] \ tyuv] || (syms, COE (dir, (v, HOLE), coercee) :: stk) => ?todo

     | O.EQUALITY $ _ || (_, []) => raise Final
     | O.EQUALITY $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ Syn.into Syn.AX || (syms, stk)
     | O.EQUALITY $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.NAT $ _ || (_, []) => raise Final
     | O.ZERO $ _ || (_, []) => raise Final
     | O.SUCC $ _ || (_, []) => raise Final
     | O.NAT_REC $ [_ \ m, _ \ n, [x,y] \ p] || (syms, stk) => COMPAT @@ m || (syms, NAT_REC (HOLE, n, (x,y,p)) :: stk)
     | O.ZERO $ _ || (syms, NAT_REC (HOLE, zer, _) :: stk) => CRITICAL @@ zer || (syms, stk)
     | O.SUCC $ [_ \ n] || (syms, NAT_REC (HOLE, zer, (x,y, succ)) :: stk) =>
       let
         val rho = VarKit.ctxFromList [(n, x), (Syn.into @@ Syn.NAT_REC (n, (zer, (x,y,succ))), y)]
       in
         CRITICAL @@ substVarenv rho succ || (syms, stk)
       end
     | O.NAT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.NAT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.INT $ _ || (_, []) => raise Final
     | O.NEGSUCC $ _ || (_, []) => raise Final
     | O.INT_REC $ [_ \ m, _ \ n, [x,y] \ p, _ \ q, [x',y'] \ r] || (syms, stk) => COMPAT @@ m || (syms, INT_REC (HOLE, n, (x,y,p), q, (x',y',r)) :: stk)
     | O.ZERO $ _ || (syms, INT_REC (HOLE, n, _, _, _) :: stk) => CRITICAL @@ n || (syms, stk)
     | O.SUCC $ [_ \ m] || (syms, INT_REC (HOLE, n, (x,y,p), _, _) :: stk) =>
       let
         val rho = VarKit.ctxFromList [(m, x), (Syn.into @@ Syn.NAT_REC (m, (n, (x,y,p))), y)]
       in
         CRITICAL @@ substVarenv rho p || (syms, stk)
       end
     | O.NEGSUCC $ [_ \ m] || (syms, INT_REC (HOLE, _, _, q, (x,y,r)) :: stk) =>
       COMPAT @@ m || (syms, NAT_REC (HOLE, q, (x,y,r)) :: stk)
     | O.INT $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.INT $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.VOID $ _ || (_, []) => raise Final

     | O.WBOOL $ _ || (_, []) => raise Final
     | O.BOOL $ _ || (_, []) => raise Final
     | O.TT $ _ || (_, []) => raise Final
     | O.FF $ _ || (_, []) => raise Final

     | O.IF $ [_ \ m, _ \ t, _ \ f] || (syms, stk) => COMPAT @@ m || (syms, IF (HOLE, t, f) :: stk)
     | O.WIF $ [[x] \ tyx, _ \ m, _ \ t, _ \ f] || (syms, stk) => COMPAT @@ m || (syms, WIF ((x, tyx), HOLE, t, f) :: stk)
     | O.TT $ _ || (syms, IF (HOLE, t, _) :: stk) => CRITICAL @@ t || (syms, stk)
     | O.TT $ _ || (syms, WIF (_, HOLE, t, _) :: stk) => CRITICAL @@ t || (syms, stk)
     | O.FF $ _ || (syms, IF (HOLE, _, f) :: stk) => CRITICAL @@ f || (syms, stk)
     | O.FF $ _ || (syms, WIF (_, HOLE, _, f) :: stk) => CRITICAL @@ f || (syms, stk)
     | O.BOOL $ _ || (syms, HCOM (_, _, cap, _) :: stk) => CRITICAL @@ cap || (syms, stk)
     | O.BOOL $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)
     | O.WBOOL $ _ || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val fcom =
           Syn.intoFcom
             {dir = dir,
              cap = cap,
              tubes = tubes}
       in
         CRITICAL @@ fcom || (syms, stk)
       end
     | O.WBOOL $ _ || (syms, COE (_, (u, HOLE), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.S1 $ _ || (_, []) => raise Final
     | O.BASE $ _ || (_, []) => raise Final
     | O.LOOP $ [_ \ r] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ Syn.into Syn.BASE || (syms, stk))
           (STEP @@ Syn.into Syn.BASE || (syms, stk))
           (fn u =>
             case stk of
               [] => raise Final
             | S1_REC (_, HOLE, _, (v, loop)) :: stk => CRITICAL @@ substVar (VarKit.toDim u, v) loop || (syms, stk)
             | _ => raise Stuck)
     | O.BASE $ _ || (syms, S1_REC (_, HOLE, base, _) :: stk) => CRITICAL @@ base || (syms, stk)
     | O.S1_REC $ [[x] \ c, _ \ m, _ \ b, [x'] \ l] || (syms, stk) => COMPAT @@ m || (syms, S1_REC ((x,c), HOLE, b, (x',l)) :: stk)
     | O.S1 $ _ || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
       let
         val fcom =
           Syn.intoFcom
             {dir = dir,
              cap = cap,
              tubes = tubes}
       in
         CRITICAL @@ fcom || (syms, stk)
       end
     | O.S1 $ _ || (syms, COE (_, (u, HOLE), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

     | O.RECORD _ $ _ || (_, []) => raise Final
     | O.TUPLE _ $ _ || (_, []) => raise Final
     | O.PROJ lbl $ [_ \ m] || (syms, stk) => COMPAT @@ m || (syms, PROJ (lbl, HOLE) :: stk)
     | O.TUPLE_UPDATE lbl $ [_ \ n, _ \ m] || (syms, stk) => COMPAT @@ m || (syms, TUPLE_UPDATE (lbl, n, HOLE) :: stk)
     | O.TUPLE lbls $ args || (syms, PROJ (lbl, HOLE) :: stk) =>
       let
         val fields = Syn.outTupleFields (lbls, args)
       in
         CRITICAL @@ Syn.Fields.lookup lbl fields || (syms, stk)
         handle Syn.Fields.Absent => raise Stuck
       end
     | O.TUPLE lbls $ args || (syms, TUPLE_UPDATE (lbl, n, HOLE) :: stk) =>
       let
         val fields = Syn.outTupleFields (lbls, args)
         val (lbls', args') = Syn.intoTupleFields @@ Syn.Fields.update (lbl, n) fields
       in
         CRITICAL @@ O.TUPLE lbls' $$ args' || (syms, stk)
       end
     | O.RECORD lbls $ args || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) => 
       (case (lbls, args) of 
           ([], []) =>
           let
             val tuple = Syn.into @@ Syn.TUPLE Syn.Fields.empty
           in
             CRITICAL @@ tuple || (syms, stk)
           end
         | (lbl :: lbls, [] \ ty :: args) =>
           let
             val (r, r') = dir
             fun proj m = Syn.into @@ Syn.PROJ (lbl, m)
             fun head s =
               Syn.intoHcom
                 {dir = (r, s),
                  ty = ty,
                  cap = proj cap,
                  tubes = mapTubes_ proj tubes}

             fun shiftField s = 
               fn (x :: xs) \ ty => xs \ substVar (head s, x) ty
                | _ => raise Fail "Impossible field"

             val u = Sym.named "u"
             val ty'u = O.RECORD lbls $$ List.map (shiftField (VarKit.toDim u)) args

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
     | O.RECORD lbls $ args || (syms, COE (dir, (u, HOLE), coercee) :: stk) =>  
       (case (lbls, args) of 
           ([], []) =>
           let
             val tuple = Syn.into @@ Syn.TUPLE Syn.Fields.empty
           in
             CRITICAL @@ tuple || (syms, stk)
           end
         | (lbl :: lbls, [] \ ty :: args) =>
           let
             val (r, r') = dir
             fun proj m = Syn.into @@ Syn.PROJ (lbl, m)
             fun head s =
               Syn.intoCoe
                 {dir = (r, s),
                  ty = (u, ty),
                  coercee = proj coercee}

             fun shiftField s = 
               fn (x :: xs) \ ty => xs \ substVar (head s, x) ty
                | _ => raise Fail "Impossible field"

             val u = Sym.named "u"
             val ty'u = O.RECORD lbls $$ List.map (shiftField (VarKit.toDim u)) args

             val tail =
               Syn.intoCoe
                 {dir = dir,
                  ty = (u, ty'u),
                  coercee = coercee}
           in
             CRITICAL @@ tail || (syms, TUPLE_UPDATE (lbl, head r', HOLE) :: stk)
           end
         | _ => raise Fail "Impossible record type")

     | O.BOX $ [_ \ r1, _ \ r2, _ \ cap, _ \ boundaries] || (syms, stk) => 
       stepBox stability ({dir = (r1, r2), cap = cap, boundaries = Syn.outBoundaries boundaries} || (syms, stk))
     | O.CAP $ [_ \ r1, _ \ r2, _ \ coercee, _ \ tubes] || (syms, stk) => 
       stepCap stability ({dir = (r1, r2), coercee = coercee, tubes = Syn.outTubes tubes} || (syms, stk))

     | O.V $ [_ \ r, _ \ a, _ \ b, _ \ e] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ a || (syms, stk))
           (STEP @@ b || (syms, stk))
           (fn u =>
             case stk of
               [] => raise Final
             | HCOM (dir, HOLE, cap, tubes) :: stk =>
                 let
                   val v = Sym.named "v"
                   val f = Syn.intoFst e
                   fun vproj m = Syn.into @@ Syn.VPROJ (r, m, f)
                   fun m' ty y = Syn.intoHcom
                     {dir = (#1 dir, y), ty = ty, cap = cap, tubes = tubes}
                   val n = Syn.intoHcom
                     {dir = dir, ty = b,
                      cap = vproj cap,
                      tubes =
                           ((VarKit.toDim u, Syn.intoDim 0), (v, Syn.intoApp (f, m' a (VarKit.toDim v))))
                        :: ((VarKit.toDim u, Syn.intoDim 1), (v, m' b (VarKit.toDim v)))
                        :: mapTubes_ vproj tubes}
                 in
                   CRITICAL @@ Syn.into (Syn.VIN (r, m' a (#2 dir), n)) || (syms, stk)
                 end
             | COE (dir, (v, HOLE), coercee) :: stk =>
                 let
                   val syms' = SymSet.remove syms v
                   val vin =
                     (* Sym.eq (u, v) is stable because v is bound *)
                     if Sym.eq (u, v) then
                       let
                         fun nFromZero s = Syn.intoCoe
                           {dir = (Syn.intoDim 0, s), ty = (v, b),
                            coercee = Syn.intoApp (Syn.intoFst (substVar (Syn.intoDim 0, v) e), coercee)}
                         fun projFromOne s = Syn.intoCoe {dir = (Syn.intoDim 1, s), ty = (v, b), coercee = coercee}
                         fun fiberFromOne s = Syn.intoFst @@ Syn.intoApp (Syn.intoSnd (substVar (s, v) e), projFromOne s)
                         fun nFromOne s t = (* t is the dimension used in the hcom to fix the zero-end. *)
                           let
                             val w = Sym.named "w"
                           in
                             Syn.intoHcom
                               {dir = (Syn.intoDim 1, t),
                                ty = substVar (s, v) b,
                                cap = projFromOne s,
                                tubes =
                                  [ ((s, Syn.intoDim 0), (w, Syn.into @@ Syn.PATH_APP (Syn.intoSnd (fiberFromOne s), VarKit.toDim w)))
                                  , ((s, Syn.intoDim 1), (w, projFromOne s)) ]}
                           end
                       in
                         branchOnDim stability syms' (#1 dir)
                           (Syn.into @@ Syn.VIN (#2 dir, coercee, nFromZero (#2 dir)))
                           (Syn.into @@ Syn.VIN (#2 dir, Syn.intoFst (fiberFromOne (#2 dir)), nFromOne (#2 dir) (Syn.intoDim 1)))
                           (fn y =>
                              let
                                fun base x =
                                  let
                                    val w = Sym.named "w"
                                  in
                                    Syn.intoCom
                                      {dir = (#1 dir, x), ty = (v, b),
                                       cap = Syn.into @@ Syn.VPROJ (#1 dir, coercee, Syn.intoFst @@ substVar (#1 dir, v) e),
                                       tubes =
                                         [ ((#1 dir, Syn.intoDim 0), (w, nFromZero (VarKit.toDim w)))
                                         , ((#1 dir, Syn.intoDim 0), (w, projFromOne (VarKit.toDim w))) ]}
                                  end
                                val wallZero =
                                  let
                                    val z = Sym.named "z"
                                    val m = Syn.intoCoe
                                      {dir = (Syn.intoDim 0, VarKit.toDim y),
                                       ty = (y, substVar (Syn.intoDim 0, v) a),
                                       coercee = substVar (Syn.intoDim 0, y) coercee}
                                  in
                                    Syn.intoAnonTuple
                                      [ m
                                      , Syn.into @@ Syn.PATH_ABS (z,
                                          Syn.intoCom
                                            {dir = (Syn.intoDim 0, VarKit.toDim y),
                                             ty = (y, substVar (Syn.intoDim 0, v) b),
                                             cap = coercee,
                                             tubes =
                                               [ ((VarKit.toDim z, Syn.intoDim 0),
                                                  (y, Syn.intoApp
                                                        (Syn.intoFst (substVar (Syn.intoDim 0, v) e), m)))
                                               , ((VarKit.toDim z, Syn.intoDim 1),
                                                  (y, base (Syn.intoDim 0))) ]}) ]
                                  end
                                val frontFiber =
                                  Syn.intoApp
                                    (Syn.intoSnd
                                      (Syn.intoApp
                                        (Syn.intoSnd (substVar (Syn.intoDim 0, v) e),
                                         base (Syn.intoDim 0))),
                                     wallZero)
                                val n =
                                  let
                                    val w = Sym.named "w"
                                  in
                                    Syn.intoHcom
                                      {dir = (Syn.intoDim 0, Syn.intoDim 1),
                                       ty = substVar (#2 dir, v) b,
                                       cap = base (#2 dir),
                                       tubes =
                                         [ ((#1 dir, Syn.intoDim 0),
                                            (w, nFromZero (#2 dir)))
                                         , ((#1 dir, Syn.intoDim 1),
                                            (w, nFromOne (#2 dir) (VarKit.toDim w)))
                                         , ((#1 dir, #2 dir),
                                            (w, Syn.into @@ Syn.VPROJ (#2 dir, coercee, Syn.intoFst @@ substVar (#2 dir, v) e)))
                                         , ((#2 dir, Syn.intoDim 0),
                                            (w, Syn.into @@ Syn.PATH_APP (Syn.intoSnd frontFiber, VarKit.toDim w))) ]}
                                  end
                              in
                                Syn.into @@ Syn.VIN (#2 dir, Syn.intoFst frontFiber, n)
                              end)
                       end
                     else
                       let
                         fun m ty s = Syn.intoCoe {dir = (#1 dir, s), ty = (v, ty), coercee = coercee}
                         val n =
                           Syn.intoCom
                             {dir = dir,
                              ty = (v, b),
                              cap = Syn.into @@ Syn.VPROJ (r, coercee, Syn.intoFst @@ substVar (#1 dir, v) e),
                              tubes =
                                [ ((r, Syn.intoDim 0),
                                   (v, Syn.intoApp (Syn.intoFst e, m a (VarKit.toDim v))))
                                , ((r, Syn.intoDim 1),
                                   (v, m b (VarKit.toDim v))) ]}
                       in
                         Syn.into @@ Syn.VIN (r, m a (#2 dir), n)
                       end
                 in
                   CRITICAL @@ vin || (syms', stk)
                 end
             | _ => raise Stuck)
     | O.VIN $ [_ \ r, _ \ m, _ \ n] || (syms, stk) =>
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
     | O.VPROJ $ [_ \ r, _ \ m, _ \ f] || (syms, stk) =>
         branchOnDim stability syms r
           (STEP @@ Syn.intoApp (f, m) || (syms, stk))
           (STEP @@ m || (syms, stk))
           (fn u => COMPAT @@ m || (syms, VPROJ (u, HOLE, f) :: stk))

     | O.UNIVERSE $ _ || (_, []) => raise Final
     | O.UNIVERSE $ (_ :: _ \ k :: _) || (syms, HCOM (dir, HOLE, cap, tubes) :: stk) =>
         let
           val fcom =
             Syn.intoFcom
               {dir = dir,
                cap = cap,
                tubes = tubes}
         in
           case Tm.out k of
             O.KCONST k $ _ =>
               (case k of
                  K.DISCRETE => CRITICAL @@ cap || (syms, stk)
                | K.KAN => CRITICAL @@ fcom || (syms, stk)
                | K.HCOM => CRITICAL @@ fcom || (syms, stk)
                | K.COE => raise Stuck
                | K.STABLE => raise Stuck)
           | _ => raise Stuck
         end
     | O.UNIVERSE $ _ || (syms, COE (_, (u, _), coercee) :: stk) => CRITICAL @@ coercee || (SymSet.remove syms u, stk)

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
