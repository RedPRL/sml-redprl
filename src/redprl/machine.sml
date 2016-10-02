functor RedPrlMachineBasis (Sig : MINI_SIGNATURE) : ABT_MACHINE_BASIS =
struct
  structure Cl = AbtClosureUtil (AbtClosure (RedPrlAbt))
  structure S = AbtMachineState (Cl)
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  structure Syn = Syntax
  type sign = Sig.sign

  exception InvalidCut

  open RedPrlAbt Cl
  infix 0 \
  infix 1 <:
  infix 2 $ `$ $$ $#

  fun @@ (f, x) = f x
  infixr @@

  structure O = RedPrlOpData and E = RedPrlError

  structure ListUtil =
  struct
    fun indexSatisfyingPredicate p =
      let
        exception NotFound
        fun go i [] = raise NotFound
          | go i (x :: xs) =
              case p x of
                 SOME x' => (i, x')
               | NONE => go (i + 1) xs
      in
        fn xs => SOME (go 0 xs) handle _ => NONE
      end
  end

  fun readParam {params,terms} =
    P.bind (fn x => Option.getOpt (Sym.Ctx.find params x, P.ret x))

  (* Extract a concrete dimension {0,1} from a dimension parameter; returns NONE in case of a dimension variable. *)
  fun asConcrete env r =
    case readParam env r of
       P.APP t => SOME t
     | _ => NONE

  (* E ⊨ r # r' *)
  fun paramsApart env (r1, r2) =
    not (P.eq Sym.eq (readParam env r1, readParam env r2))

  fun reverseDir (r1, r2) = (r2, r1)

  (* computation rules for Kan compositions at base type *)
  fun stepAtomicHcom exts (r, r') (_ \ cap) tubes env =
    case ListUtil.indexSatisfyingPredicate (asConcrete env) exts of
       SOME (i, c) =>
         let
           val j = case c of P.DIM0 => i * 2 | P.DIM1 => i * 2 + 1 | _ => raise Match
           val ([y],_) \ tube = List.nth (tubes, j)
         in
           S.STEP @@ tube <: Cl.insertSym env y r'
         end
     | NONE =>
         if paramsApart env (r,r') then
           S.VAL
         else
           S.STEP @@ cap <: env

  structure ParamElem =
  struct
    type t = param
    val eq = P.eq Sym.eq
  end

  structure SymEnvUtil = ContextUtil (structure Ctx = Sym.Ctx and Elem = ParamElem)

  fun unifyCustomOperator (entry : Sig.entry) (ps : param list) (es : abt bview list) : metaenv * symenv =
    let
      val {params, arguments, ...} = entry
      val srho = ListPair.foldl (fn ((u,_), p, ctx) => Sym.Ctx.insert ctx u p) Sym.Ctx.empty (params, ps)
      val mrho = ListPair.foldl (fn ((x, vl), e, ctx) => Metavar.Ctx.insert ctx x (checkb (e, vl))) Metavar.Ctx.empty (arguments, es)
    in
      (mrho, srho)
    end

  structure Tac =
  struct
    val autoStep = O.MONO O.RULE_AUTO_STEP $$ []

    fun elim u =
      O.POLY (O.RULE_ELIM u) $$ []

    fun all t =
      O.MONO O.MTAC_ALL $$ [([],[]) \ t]

    fun each ts =
      O.MONO (O.MTAC_EACH (List.length ts)) $$ List.map (fn t => ([],[]) \ t) ts

    fun seq mt bs t =
      let
        val (us, sorts) = ListPair.unzip bs
      in
        O.MONO (O.TAC_SEQ sorts) $$ [([],[]) \ mt, (us, []) \ t]
      end

    fun try t =
      O.MONO O.TAC_ORELSE $$ [([],[]) \ t, ([],[]) \ O.MONO O.RULE_ID $$ []]

    fun progress t =
      O.MONO O.TAC_PROGRESS $$ [([],[]) \ t]

    fun fromMtac mt =
      seq mt [] (O.MONO O.RULE_ID $$ [])

    fun then' t1 t2 =
      seq (all t1) [] t2

    fun repeat t =
      let
        val x = Var.named "t"
      in
        O.MONO O.TAC_REC $$ [([],[x]) \ try (then' (progress t) (check (`x, O.TAC)))]
      end

    fun cut jdg =
      O.MONO O.RULE_CUT $$ [([],[]) \ jdg]
  end


  (* [step] tells our machine how to proceed when computing a term: is it a value,
   * can it step without inspecting the values of its arguments, or does it need to inspect one
   * of its arguments (i.e. it is a cut)? *)
  fun step sign =
    fn O.MONO O.DFUN `$ _ <: _ => S.VAL
     | O.MONO O.LAM `$ _ <: _ => S.VAL
     | O.MONO O.AP `$ [_ \ m, _ \ n] <: env =>
         S.CUT
           @@ (O.MONO O.AP `$ [([],[]) \ S.HOLE, ([],[]) \ S.% n], m)
           <: env

     | O.MONO O.DPROD `$ _ <: _ => S.VAL
     | O.MONO O.PAIR `$ _ <: _ => S.VAL
     | O.MONO O.FST `$ [_ \ m] <: env =>
         S.CUT
          @@ (O.MONO O.FST `$ [([],[]) \ S.HOLE], m)
          <: env
     | O.MONO O.SND `$ [_ \ m] <: env =>
         S.CUT
          @@ (O.MONO O.SND `$ [([],[]) \ S.HOLE], m)
          <: env

     | O.MONO O.BOOL `$ _ <: _ => S.VAL
     | O.MONO O.TRUE `$ _ <: _ => S.VAL
     | O.MONO O.FALSE `$ _ <: _ => S.VAL
     | O.MONO O.IF `$ [(_,[x]) \ cx, _ \ b, _ \ t, _ \ f] <: env =>
         S.CUT
           @@ (O.MONO O.IF `$ [([],[x]) \ S.% cx, ([],[]) \ S.HOLE, ([],[]) \ S.% t, ([],[]) \ S.% f], b)
           <: env

     | O.MONO O.S1 `$ _ <: _ => S.VAL
     | O.MONO O.BASE `$ _ <: _ => S.VAL
     | O.POLY (O.LOOP r) `$ _ <: env =>
         (case readParam env r of
             P.VAR a => S.VAL
           | P.APP P.DIM0 => S.STEP @@ O.MONO O.BASE $$ [] <: env
           | P.APP P.DIM1 => S.STEP @@ O.MONO O.BASE $$ [] <: env
           | P.APP _ => raise Match)

     | O.MONO O.S1_ELIM `$ [(_,[x]) \ cx, _ \ m, _ \ b, ([u],_) \ l] <: env =>
         S.CUT
           @@ (O.MONO O.S1_ELIM `$ [([],[x]) \ S.% cx, ([],[]) \ S.HOLE, ([],[]) \ S.% b, ([u],[]) \ S.% l], m)
           <: env

     | O.MONO O.ID_TY `$ _ <: _ => S.VAL
     | O.MONO O.ID_ABS `$ _ <: _ => S.VAL
     | O.POLY (O.ID_AP r) `$ [_ \ m] <: env =>
         S.CUT
           @@ (O.POLY (O.ID_AP r) `$ [([],[]) \ S.HOLE], m)
           <: env

     | O.MONO O.AX `$ _ <: _ => S.VAL

     | O.MONO (O.REFINE _) `$ _ <: _ => S.VAL
     | O.MONO (O.EXTRACT tau) `$ [_ \ thm] <: env =>
         S.CUT
           @@ (O.MONO (O.EXTRACT tau) `$ [([],[]) \ S.HOLE], thm)
           <: env

     | O.MONO (O.TAC_SEQ _) `$ _ <: _ => S.VAL
     | O.MONO O.TAC_ORELSE `$ _ <: _ => S.VAL
     | O.MONO O.TAC_REC `$ _ <: _ => S.VAL
     | O.MONO O.TAC_PROGRESS `$ _ <: _ => S.VAL

     | O.MONO O.RULE_ID `$ _ <: _ => S.VAL
     | O.MONO O.RULE_EVAL_GOAL `$ _ <: _ => S.VAL
     | O.MONO O.RULE_CEQUIV_REFL `$ _ <: _ => S.VAL
     | O.MONO O.RULE_WITNESS `$ _ <: _ => S.VAL
     | O.MONO O.RULE_SYMMETRY `$ _ <: _ => S.VAL
     | O.MONO O.RULE_AUTO_STEP `$ _ <: _ => S.VAL
     | O.MONO O.RULE_AUTO `$ _ <: env =>
         S.STEP
           @@ Tac.repeat Tac.autoStep
           <: env
     | O.POLY (O.RULE_HYP _) `$ _ <: _ => S.VAL
     | O.POLY (O.RULE_ELIM _) `$ _ <: _ => S.VAL
     | O.MONO O.RULE_HEAD_EXP `$ _ <: _ => S.VAL
     | O.MONO O.RULE_CUT `$ _ <: _ => S.VAL
     | O.MONO (O.RULE_LEMMA (true, tau)) `$ _ <: _ => S.VAL
     | O.MONO (O.RULE_LEMMA (false, tau)) `$ [_ \ thm] <: env =>
         S.CUT
           @@ (O.MONO (O.RULE_LEMMA (false, tau)) `$ [([],[]) \ S.HOLE], thm)
           <: env

     | O.MONO O.DEV_LET `$ [_ \ jdg, _ \ tac1, ([u],_) \ tac2] <: env =>
         S.STEP
          @@ Tac.seq (Tac.all (Tac.cut jdg)) [(u, P.HYP)] (Tac.fromMtac (Tac.each [tac2,tac1]))
          <: env
     | O.MONO O.DEV_FUN_INTRO `$ [([u], _) \ t] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all Tac.autoStep) [(u, P.HYP)] (Tac.fromMtac (Tac.each [t]))
           <: env
     | O.MONO O.DEV_DPROD_INTRO `$ [_ \ t1, _ \ t2] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all Tac.autoStep) [] (Tac.fromMtac (Tac.each [t1, t2]))
           <: env
     | O.MONO O.DEV_PATH_INTRO `$ [([u], _) \ t] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all Tac.autoStep) [(u, P.DIM)] (Tac.fromMtac (Tac.each [t]))
           <: env
     | O.POLY (O.DEV_BOOL_ELIM z) `$ [_ \ t1, _ \ t2] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all (Tac.elim z)) [] (Tac.fromMtac (Tac.each [t1,t2]))
           <: env
     | O.POLY (O.DEV_S1_ELIM z) `$ [_ \ t1, ([v],_) \ t2] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all (Tac.elim z)) [(v, P.DIM)] (Tac.fromMtac (Tac.each [t1,t2]))
           <: env
     | O.POLY (O.DEV_DFUN_ELIM z) `$ [_ \ t1, ([x,p],_) \ t2] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all (Tac.elim z)) [(x, P.HYP), (p, P.HYP)] (Tac.fromMtac (Tac.each [t1,t2]))
           <: env

     | O.POLY (O.DEV_DPROD_ELIM z) `$ [([x,y], _) \ t] <: env =>
         S.STEP
           @@ Tac.seq (Tac.all (Tac.elim z)) [(x, P.HYP), (y, P.HYP)] (Tac.fromMtac (Tac.each [t]))
           <: env

     | O.MONO O.MTAC_ALL `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_EACH n) `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_FOCUS i) `$ _ <: _ => S.VAL

     | O.MONO O.JDG_EQ `$ _ <: _ => S.VAL
     | O.MONO O.JDG_CEQ `$ _ <: _ => S.VAL
     | O.MONO O.JDG_MEM `$ _ <: _ => S.VAL
     | O.MONO O.JDG_EQ_TYPE `$ _ <: _ => S.VAL
     | O.MONO O.JDG_TYPE `$ _ <: _ => S.VAL
     | O.MONO O.JDG_TRUE `$ _ <: _ => S.VAL
     | O.MONO O.JDG_SYNTH `$ _ <: _ => S.VAL

     | O.POLY (O.UNIV _) `$ _ <: _ => S.VAL

     | (cust as O.POLY (O.CUST (opid, ps, ar))) `$ args <: env =>
         let
           val entry as {definiens,...} = Sig.lookup sign opid
           val (mrho, srho) = unifyCustomOperator entry (List.map #1 ps) args
           val definiens' = substMetaenv mrho definiens
           val env' = {params = SymEnvUtil.union (#params env, srho), terms = #terms env}
         in
           S.STEP @@ definiens' <: env'
         end

     | (hcom as O.POLY (O.HCOM (O.TAG_NONE, exts, dir))) `$ (_ \ ty) :: cap :: tubes <: env =>
         S.CUT
           @@ (hcom `$ (([],[]) \ S.HOLE) :: List.map (mapBind S.%) (cap :: tubes), ty)
           <: env

     | O.POLY (O.HCOM (O.TAG_BOOL, exts, dir)) `$ cap :: tubes <: env =>
         stepAtomicHcom exts dir cap tubes env

     | O.POLY (O.HCOM (O.TAG_S1, exts, dir)) `$ cap :: tubes <: env =>
         stepAtomicHcom exts dir cap tubes env

     | O.POLY (O.HCOM (O.TAG_DFUN, exts, dir)) `$ (_ \ a) :: ((_,[x]) \ bx) :: cap :: tubes <: env =>
         let
           fun apx m = O.MONO O.AP $$ [([],[]) \ m, ([],[]) \ Abt.check (`x, O.EXP)]
           val hcomx = O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) $$ (([],[]) \ bx) :: List.map (mapBind apx) (cap :: tubes)
           val lam = Syn.into @@ Syn.LAM (x, hcomx)
         in
           S.STEP @@ lam <: env
         end
     | O.POLY (O.HCOM (O.TAG_DPROD, exts, dir)) `$ (_ \ a) :: ((_,[x]) \ bx) :: (_ \ cap) :: tubes <: env =>
         let
           val fst = Syn.into o Syn.FST
           val snd = Syn.into o Syn.SND
           fun hcom1 r = O.POLY (O.HCOM (O.TAG_NONE, exts, (#1 dir, r))) $$ (([],[]) \ a) :: (([],[]) \ fst cap) :: List.map (mapBind fst) tubes

           val v = Sym.named "v"
           val com = Syn.heteroCom (exts, dir) ((v, substVar (hcom1 (P.ret v), x) bx), snd cap, List.map (mapBind snd) tubes)
           val pair = Syn.into @@ Syn.PAIR (hcom1 (#2 dir), com)
         in
           S.STEP @@ pair <: env
         end

     | (coe as O.POLY (O.COE (O.TAG_NONE, dir))) `$ [([u],_) \ a, _ \ m] <: env =>
         S.CUT
           @@ (coe `$ [([u],[]) \ S.HOLE, ([],[]) \ S.% m], a)
           <: env

     | O.POLY (O.COE (O.TAG_BOOL, dir)) `$ [_ \ m] <: env =>
         S.STEP @@ m <: env

     | O.POLY (O.COE (O.TAG_S1, dir)) `$ [_ \ m] <: env =>
         S.STEP @@ m <: env

     | O.POLY (O.COE (O.TAG_DFUN, dir as (r, r'))) `$ [([u],_) \ a, ([v],[x]) \ bvx, _ \ m] <: env =>
         let
           fun coea r'' = O.POLY (O.COE (O.TAG_NONE, (r', r''))) $$ [([u],[]) \ a, ([],[]) \ check (`x, O.EXP)]
           val bcoe = substVar (coea (P.ret v), x) bvx
           val app = O.MONO O.AP $$ [([],[]) \ m, ([],[]) \ coea r]
           val coeR = O.POLY (O.COE (O.TAG_NONE, dir)) $$ [([v],[]) \ bcoe, ([],[]) \ app]
           val lam = O.MONO O.LAM $$ [([],[x]) \ coeR]
         in
           S.STEP @@ lam <: env
         end

     | O.POLY (O.COE (O.TAG_DPROD, dir)) `$ [([u],_) \ a, ([v],[x]) \ bvx, _ \ m] <: env =>
         let
           fun coe1 r = O.POLY (O.COE (O.TAG_NONE, (#1 dir, r))) $$ [([u],[]) \ a, ([],[]) \ Syn.into (Syn.FST m)]
           val coe2 = O.POLY (O.COE (O.TAG_NONE, (#1 dir, #2 dir))) $$ [([v], []) \ substVar (coe1 (P.ret v), x) bvx, ([],[]) \ Syn.into (Syn.SND m)]
           val pair = Syn.into @@ Syn.PAIR (coe1 (#2 dir), coe2)
         in
           S.STEP @@ pair <: env
         end

     | th `$ es <: env => raise E.error [E.% "Machine encountered unrecognized term", E.! (th $$ es)]

  (* [cut] tells the machine how to plug a value into a hole in a stack frame. As a rule of thumb,
   * any time you return [CUT] in the [step] judgment, you should add a corresponding rule to [cut]. *)
  fun cut sign =
    fn (O.MONO O.AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ O.MONO O.LAM `$ [(_,[x]) \ mx] <: env) => mx <: Cl.insertVar env x cl
     | (O.MONO O.FST `$ [_ \ S.HOLE], _ \ O.MONO O.PAIR `$ [_ \ m, _ \ n] <: env) => m <: env
     | (O.MONO O.SND `$ [_ \ S.HOLE], _ \ O.MONO O.PAIR `$ [_ \ m, _ \ n] <: env) => n <: env

     | (O.MONO (O.EXTRACT _) `$ [_ \ S.HOLE], _ \ O.MONO (O.REFINE (true, _)) `$ [_, _, _ \ m] <: env) => m <: env
     | (O.MONO (O.RULE_LEMMA (_, tau)) `$ [_ \ S.HOLE], _ \ O.MONO (O.REFINE (true, tau')) `$ [goal, script, evd] <: env) =>
         O.MONO (O.RULE_LEMMA (true, tau)) $$ [([],[]) \ O.MONO (O.REFINE (true, tau')) $$ [goal, script, evd]] <: env
     | (O.MONO O.IF `$ [_, _ \ S.HOLE, _ \ S.% cl, _], _ \ O.MONO O.TRUE `$ _ <: _) => cl
     | (O.MONO O.IF `$ [_, _ \ S.HOLE, _, _ \ S.% cl], _ \ O.MONO O.FALSE `$ _ <: _) => cl
     | (O.MONO O.IF `$ [(_,[x]) \ S.% cx, _ \ S.HOLE, _ \ S.% t, _ \ S.% f], _ \ O.POLY (O.HCOM (O.TAG_BOOL, exts, dir)) `$ (_ \ cap) :: tubes <: env) =>
         let
           val (r, r') = dir
           val cx' = Cl.force cx
           val t' = Cl.force t
           val f' = Cl.force f

           val v = Sym.named "v"
           val hv = O.POLY (O.HCOM (O.TAG_BOOL, exts, (r, P.ret v))) $$ (([],[]) \ cap) :: tubes
           val chv = substVar (hv, x) cx'
           fun mkIf m = Syn.into @@ Syn.IF ((x, cx'), m, (t', f'))
         in
           Syn.heteroCom (exts, dir) ((v, chv), mkIf cap, List.map (mapBind mkIf) tubes) <: env
         end

     | (O.MONO O.S1_ELIM `$ [(_,[x]) \ S.% cx, _ \ S.HOLE, _ \ S.% b, ([u],_) \ S.% l], _ \ O.MONO O.BASE `$ _ <: _) => b
     | (O.MONO O.S1_ELIM `$ [(_,[x]) \ S.% cx, _ \ S.HOLE, _ \ S.% b, ([u],_) \ S.% (l <: envL)], _ \ O.POLY (O.LOOP r) `$ _ <: env) =>
         let
           val r' = Cl.forceParam (r <: env)
         in
           l <: Cl.insertSym envL u r'
         end
     | (O.MONO O.S1_ELIM `$ [(_,[x]) \ S.% cx, _ \ S.HOLE, _ \ S.% b, ([u],_) \ S.% l], _ \ O.POLY (O.HCOM (O.TAG_S1, exts, dir)) `$ (_ \ cap) :: tubes <: env) =>
         let
           val (r, r') = dir
           val cx' = Cl.force cx
           val b' = Cl.force b
           val l' = Cl.force l

           val v = Sym.named "v"
           val hv = O.POLY (O.HCOM (O.TAG_S1, exts, (r, P.ret v))) $$ (([],[]) \ cap) :: tubes
           val chv = substVar (hv, x) cx'
           fun mkElim m = Syn.into @@ Syn.S1_ELIM ((x, cx'), m, (b', (u, l')))
         in
           Syn.heteroCom (exts, dir) ((v, chv), mkElim cap, List.map (mapBind mkElim) tubes) <: env
         end


     | (O.POLY (O.ID_AP r) `$ [_ \ S.HOLE], _ \ O.MONO O.ID_ABS `$ [([u],_) \ m] <: env) =>
         m <: Cl.insertSym env u r

     | (O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.BOOL `$ _ <: env) =>
         let
           val args = List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args
           val hcom = O.POLY @@ O.HCOM (O.TAG_BOOL, exts, dir)
         in
           hcom $$ args <: env
         end
     | (O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.S1 `$ _ <: env) =>
         let
           val args = List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args
           val hcom = O.POLY @@ O.HCOM (O.TAG_S1, exts, dir)
         in
           hcom $$ args <: env
         end
     | (O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.DFUN `$ [a, b] <: env) =>
         let
           val args = List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args
           val hcom = O.POLY @@ O.HCOM (O.TAG_DFUN, exts, dir)
         in
           hcom $$ a :: b :: args <: env
         end
     | (O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.DPROD `$ [a, b] <: env) =>
         let
           val args = List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args
           val hcom = O.POLY @@ O.HCOM (O.TAG_DPROD, exts, dir)
         in
           hcom $$ a :: b :: args <: env
         end

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.BOOL `$ _ <: env) =>
         O.POLY (O.COE (O.TAG_BOOL, dir)) $$ [([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.S1 `$ _ <: env) =>
         O.POLY (O.COE (O.TAG_S1, dir)) $$ [([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.DFUN `$ [_\ a, (_,[x]) \ bx] <: env) =>
         O.POLY (O.COE (O.TAG_DFUN, dir)) $$ [([u], []) \ a, ([u],[x]) \ bx, ([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.DPROD `$ [_\ a, (_,[x]) \ bx] <: env) =>
         O.POLY (O.COE (O.TAG_DPROD, dir)) $$ [([u], []) \ a, ([u],[x]) \ bx, ([],[]) \ Cl.force cl] <: env

     | _ => raise InvalidCut
end

(* From the above definitions, we are able to generate a complete machine implementation,
 * which deals with all the bureaucratic aspects of computation: variables, congruence
 * rules, etc. The supremacy of Standard ML in action! *)
 functor RedPrlMachine (Sig : MINI_SIGNATURE) = AbtMachineUtil (AbtMachine (RedPrlMachineBasis (Sig)))
