functor RedPrlMachineBasis (Sig : MINI_SIGNATURE) : ABT_MACHINE_BASIS =
struct
  structure Cl = AbtClosureUtil (AbtClosure (RedPrlAbt))
  structure S = AbtMachineState (Cl)
  structure P = struct open RedPrlSortData RedPrlParamData RedPrlParameterTerm end
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
           val j = case c of P.DIM0 => i * 2 | P.DIM1 => i * 2 + 1
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

  structure Tac =
  struct
    val autoStep = O.MONO O.RULE_AUTO_STEP $$ []

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

     | O.MONO O.S_BOOL `$ _ <: _ => S.VAL
     | O.MONO O.S_IF `$ [_ \ b, _ \ t, _ \ f] <: env =>
         S.CUT
           @@ (O.MONO O.S_IF `$ [([],[]) \ S.HOLE, ([],[]) \ S.% t, ([],[]) \ S.% f], b)
           <: env

     | O.MONO O.S1 `$ _ <: _ => S.VAL
     | O.MONO O.BASE `$ _ <: _ => S.VAL
     | O.POLY (O.LOOP r) `$ _ <: env =>
         (case readParam env r of
             P.VAR a => S.VAL
           | P.APP P.DIM0 => S.STEP @@ O.MONO O.BASE $$ [] <: env
           | P.APP P.DIM1 => S.STEP @@ O.MONO O.BASE $$ [] <: env)

     | O.MONO O.S1_ELIM `$ [(_,[x]) \ cx, _ \ m, _ \ b, ([u],_) \ l] <: env =>
         S.CUT
           @@ (O.MONO O.S1_ELIM `$ [([],[x]) \ S.% cx, ([],[]) \ S.HOLE, ([],[]) \ S.% b, ([u],[]) \ S.% l], m)
           <: env

     | O.MONO O.PATH_TY `$ _ <: _ => S.VAL
     | O.MONO O.PATH_ABS `$ _ <: _ => S.VAL
     | O.POLY (O.PATH_AP r) `$ [_ \ m] <: env =>
         S.CUT
           @@ (O.POLY (O.PATH_AP r) `$ [([],[]) \ S.HOLE], m)
           <: env


     | O.MONO O.AX `$ _ <: _ => S.VAL

     | O.MONO (O.MTAC_SEQ _) `$ _ <: _ => S.VAL
     | O.MONO O.MTAC_ORELSE `$ _ <: _ => S.VAL
     | O.MONO O.MTAC_REC `$ _ <: _ => S.VAL
     | O.MONO O.MTAC_REPEAT `$ [_ \ mt] <: env =>
         let
           val x = Var.named "x"
           val xtm = check (`x, O.MTAC)
           val mtrec = O.MONO O.MTAC_REC $$ [([],[x]) \ Tac.mtry (Tac.seq (Tac.mprogress mt) [] xtm)]
         in
           S.STEP
             @@ mtrec
             <: env
         end

     | O.MONO (O.MTAC_HOLE _) `$ _ <: _ => S.VAL

     | O.MONO O.TAC_MTAC `$ _ <: _ => S.VAL

     | O.MONO O.RULE_ID `$ _ <: _ => S.VAL
     | O.MONO O.RULE_EVAL_GOAL `$ _ <: _ => S.VAL
     | O.MONO O.RULE_CEQUIV_REFL `$ _ <: _ => S.VAL
     | O.MONO O.RULE_WITNESS `$ _ <: _ => S.VAL
     | O.MONO O.RULE_SYMMETRY `$ _ <: _ => S.VAL
     | O.MONO O.RULE_AUTO_STEP `$ _ <: _ => S.VAL
     | O.MONO O.MTAC_AUTO `$ _ <: env =>
         S.STEP
           @@ Tac.multirepeat (Tac.all (Tac.try Tac.autoStep))
           <: env
     | O.POLY (O.RULE_HYP _) `$ _ <: _ => S.VAL
     | O.POLY (O.RULE_ELIM _) `$ _ <: _ => S.VAL
     | O.MONO O.RULE_HEAD_EXP `$ _ <: _ => S.VAL
     | O.MONO O.RULE_CUT `$ _ <: _ => S.VAL
     | O.POLY (O.RULE_UNFOLD _) `$ _ <: _ => S.VAL
     | O.POLY (O.RULE_LEMMA _) `$ _ <: _ => S.VAL
     
     | O.MONO O.DEV_LET `$ [_ \ jdg, _ \ tac1, ([u],_) \ tac2] <: env =>
         S.STEP
          @@ Tac.mtac (Tac.seq (Tac.all (Tac.cut jdg)) [(u, P.HYP O.EXP)] (Tac.each [tac2,tac1]))
          <: env
     | O.MONO O.DEV_DFUN_INTRO `$ [([u], _) \ t] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all Tac.autoStep) [(u, P.HYP O.EXP)] (Tac.each [t]))
           <: env
     | O.MONO O.DEV_DPROD_INTRO `$ [_ \ t1, _ \ t2] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all Tac.autoStep) [] (Tac.each [t1, t2]))
           <: env
     | O.MONO O.DEV_PATH_INTRO `$ [([u], _) \ t] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all Tac.autoStep) [(u, P.DIM)] (Tac.each [t]))
           <: env
     | O.POLY (O.DEV_BOOL_ELIM z) `$ [_ \ t1, _ \ t2] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [] (Tac.each [t1,t2]))
           <: env
     | O.POLY (O.DEV_S1_ELIM z) `$ [_ \ t1, ([v],_) \ t2] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(v, P.DIM)] (Tac.each [t1,t2]))
           <: env
     | O.POLY (O.DEV_DFUN_ELIM z) `$ [_ \ t1, ([x,p],_) \ t2] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(x, P.HYP O.EXP), (p, P.HYP O.EXP)] (Tac.each [t1,t2]))
           <: env

     | O.POLY (O.DEV_DPROD_ELIM z) `$ [([x,y], _) \ t] <: env =>
         S.STEP
           @@ Tac.mtac (Tac.seq (Tac.all (Tac.elim (z, O.EXP))) [(x, P.HYP O.EXP), (y, P.HYP O.EXP)] (Tac.each [t]))
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

     | (cust as O.POLY (O.CUST (opid, ps, ar))) `$ args <: env =>
         let
           val entry as {state,...} = Sig.lookup sign opid
           val Lcf.|> (subgoals, evidence) = state
           val term = Sig.extract state
           val _ = if Lcf.Tl.isEmpty subgoals then () else raise Fail "custom operator not yet fully defined!"
           val (mrho, srho) = Sig.unifyCustomOperator entry (List.map #1 ps) args
           val term' = substMetaenv mrho term
           val env' = {params = SymEnvUtil.union (#params env, srho), terms = #terms env}
         in
           S.STEP @@ term' <: env'
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

     | O.POLY (O.HCOM (O.TAG_PATH, exts, dir)) `$ (([u],_) \ a) :: (_ \ p0) :: (_ \ p1) :: (_ \ cap) :: tubes <: env =>
         let
           fun ap m = Syn.into @@ Syn.PATH_AP (m, P.ret u)
           val w = Sym.named "w"
           val tubes' = List.map (mapBind ap) tubes @ [([w],[]) \ p0, ([w],[]) \ p1]
           val hcom = O.POLY (O.HCOM (O.TAG_NONE, exts @ [P.ret u], dir)) $$ (([],[]) \ a) :: (([],[]) \ ap cap) :: tubes'
           val path = Syn.into @@ Syn.PATH_ABS (u, raise Match)
         in
           S.STEP @@ path <: env
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

     | O.POLY (O.COE (O.TAG_PATH, dir)) `$ [([u,v],_) \ auv, p0, p1, _ \ m] <: env =>
         let
           val com = Syn.heteroCom ([P.ret v], dir) ((u, auv), Syn.into @@ Syn.PATH_AP (m, P.ret u), [p0, p1])
         in
           S.STEP @@ com <: env
         end

     | th `$ es <: env => raise E.error [E.% "Machine encountered unrecognized term", E.! (th $$ es)]

  (* [cut] tells the machine how to plug a value into a hole in a stack frame. As a rule of thumb,
   * any time you return [CUT] in the [step] judgment, you should add a corresponding rule to [cut]. *)
  fun cut sign =
    fn (O.MONO O.AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ O.MONO O.LAM `$ [(_,[x]) \ mx] <: env) => mx <: Cl.insertVar env x cl
     | (O.MONO O.FST `$ [_ \ S.HOLE], _ \ O.MONO O.PAIR `$ [_ \ m, _ \ n] <: env) => m <: env
     | (O.MONO O.SND `$ [_ \ S.HOLE], _ \ O.MONO O.PAIR `$ [_ \ m, _ \ n] <: env) => n <: env

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

     | (O.MONO O.S_IF `$ [_ \ S.HOLE, _ \ S.% t, _ \ S.% f], _ \ O.MONO O.TRUE `$ _ <: _) => t
     | (O.MONO O.S_IF `$ [_ \ S.HOLE, _ \ S.% t, _ \ S.% f], _ \ O.MONO O.FALSE `$ _ <: _) => f

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


     | (O.POLY (O.PATH_AP r) `$ [_ \ S.HOLE], _ \ O.MONO O.PATH_ABS `$ [([u],_) \ m] <: env) =>
         m <: Cl.insertSym env u r

     | (O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.BOOL `$ _ <: env) =>
         let
           val args = List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args
           val hcom = O.POLY @@ O.HCOM (O.TAG_BOOL, exts, dir)
         in
           hcom $$ args <: env
         end

     | (O.POLY (O.HCOM (O.TAG_NONE, exts, dir)) `$ ((_ \ S.HOLE) :: (_ \ S.% cap) :: args), _ \ O.MONO O.S_BOOL `$ _ <: env) =>
         cap

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

     | (O.POLY (O.HCOM (O.TAG_PATH, exts, dir)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.PATH_TY `$ [a, p0, p1] <: env) =>
         let
           val args = List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args
           val hcom = O.POLY @@ O.HCOM (O.TAG_PATH, exts, dir)
         in
           hcom $$ a :: p0 :: p1 :: args <: env
         end

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.BOOL `$ _ <: env) =>
         O.POLY (O.COE (O.TAG_BOOL, dir)) $$ [([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.S_BOOL `$ _ <: env) =>
         cl

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.S1 `$ _ <: env) =>
         O.POLY (O.COE (O.TAG_S1, dir)) $$ [([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.DFUN `$ [_\ a, (_,[x]) \ bx] <: env) =>
         O.POLY (O.COE (O.TAG_DFUN, dir)) $$ [([u], []) \ a, ([u],[x]) \ bx, ([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.DPROD `$ [_\ a, (_,[x]) \ bx] <: env) =>
         O.POLY (O.COE (O.TAG_DPROD, dir)) $$ [([u], []) \ a, ([u],[x]) \ bx, ([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.PATH_TY `$ [([v],_) \ a, _ \ p0, _ \ p1] <: env) =>
         O.POLY (O.COE (O.TAG_PATH, dir)) $$ [([u,v], []) \ a, ([u],[]) \ p0, ([u],[]) \ p1, ([],[]) \ Cl.force cl] <: env

     | _ => raise InvalidCut
end

(* From the above definitions, we are able to generate a complete machine implementation,
 * which deals with all the bureaucratic aspects of computation: variables, congruence
 * rules, etc. The supremacy of Standard ML in action! *)
 functor RedPrlMachine (Sig : MINI_SIGNATURE) = AbtMachineUtil (AbtMachine (RedPrlMachineBasis (Sig)))
