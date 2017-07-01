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

  fun forceSpan ((r1, r2) <: env) =
    (Cl.forceParam (r1 <: env), Cl.forceParam (r2 <: env))

  fun forceSpans (ss <: env) = List.map (fn s => forceSpan (s <: env)) ss

  fun forceSList args =
    List.map (mapBind (fn S.% cl => Cl.force cl | _ => raise Match)) args

  fun equationPair u = [(P.VAR u, P.APP P.DIM0), (P.VAR u, P.APP P.DIM1)]

  (* computation rules for formal compositions *)
  fun stepFcom ((r, r'), eqs) ((_ \ cap) :: tubes) env =
  let
    val (r, r') = forceSpan ((r, r') <: env)
    val eqs = forceSpans (eqs <: env)
  in
    if P.eq Sym.eq (r, r') then S.STEP @@ cap <: env
    else let
      (* todo: change the generic machine so that we can return the partially
       * forced value. *)
      fun checkTubes [] [] = S.VAL
        | checkTubes (eq :: eqs) ((([y],_) \ tube) :: ts) =
            if P.eq Sym.eq eq
            then S.STEP @@ tube <: Cl.insertSym env y r'
            else checkTubes eqs ts
        | checkTubes _ _ = raise Fail "fcom has different numbers of equations and tubes."
    in
      checkTubes eqs tubes
    end
  end

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
    fn O.MONO O.AX `$ _ <: _ => S.VAL

     | O.POLY (O.FCOM params) `$ args <: env =>
         stepFcom params args env

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

     | O.MONO O.VOID `$ _ <: _ => S.VAL

     | O.MONO O.S1 `$ _ <: _ => S.VAL
     | O.MONO O.BASE `$ _ <: _ => S.VAL
     | O.POLY (O.LOOP r) `$ _ <: env =>
         (case Cl.forceParam (r <: env) of
             P.VAR _ => S.VAL
           | P.APP P.DIM0 => S.STEP @@ O.MONO O.BASE $$ [] <: env
           | P.APP P.DIM1 => S.STEP @@ O.MONO O.BASE $$ [] <: env)
     | O.MONO O.S1_ELIM `$ [(_,[x]) \ cx, _ \ m, _ \ b, ([u],_) \ l] <: env =>
         S.CUT
           @@ (O.MONO O.S1_ELIM `$ [([],[x]) \ S.% cx, ([],[]) \ S.HOLE, ([],[]) \ S.% b, ([u],[]) \ S.% l], m)
           <: env

     | O.MONO O.DFUN `$ _ <: _ => S.VAL
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

     | O.MONO O.PATH_TY `$ _ <: _ => S.VAL
     | O.MONO O.PATH_ABS `$ _ <: _ => S.VAL
     | O.POLY (O.PATH_AP r) `$ [_ \ m] <: env =>
         S.CUT
           @@ (O.POLY (O.PATH_AP r) `$ [([],[]) \ S.HOLE], m)
           <: env

     | (hcom as O.POLY (O.HCOM _)) `$ (_ \ ty) :: cap :: tubes <: env =>
         S.CUT
           @@ (hcom `$ (([],[]) \ S.HOLE) :: List.map (mapBind S.%) (cap :: tubes), ty)
           <: env
     | (coe as O.POLY (O.COE _)) `$ [([u],_) \ a, _ \ m] <: env =>
         S.CUT
           @@ (coe `$ [([u],[]) \ S.HOLE, ([],[]) \ S.% m], a)
           <: env
     | O.POLY (O.COM (dir as (r, r'), eqs)) `$ (([u],_) \ a) :: (_ \ cap) :: tubes <: env =>
         let
           fun coe s m = Syn.intoCoe (s, r') ((u, a), m)
           fun goTube (([v],_) \ n) = ([v],[]) \ coe (P.ret v) n
             | goTube _ = raise Fail "RedPrlMachineBasis.step: malformed COM tubes"
         in
           S.STEP
             @@ (O.POLY (O.HCOM (dir, eqs)) $$
                    (([],[]) \ substSymbol (r', u) a)
                 :: (([],[]) \ coe r cap)
                 :: List.map goTube tubes)
             <: env
         end

     (* tactic *)

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
     | O.MONO O.RULE_EXACT `$ _ <: _ => S.VAL
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
     | O.POLY (O.RULE_CUT_LEMMA _) `$ _ <: _ => S.VAL

     | O.MONO (O.DEV_LET tau) `$ [_ \ jdg, _ \ tac1, ([u],_) \ tac2] <: env =>
         let
           val catjdg = RedPrlCategoricalJudgment.fromAbt jdg
           val tau = RedPrlCategoricalJudgment.synthesis catjdg
         in
           S.STEP
             @@ Tac.mtac (Tac.seq (Tac.all (Tac.cut jdg)) [(u, P.HYP tau)] (Tac.each [tac1,tac2]))
             <: env
          end
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
     | O.MONO (O.MTAC_EACH _) `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_FOCUS _) `$ _ <: _ => S.VAL

     | O.MONO O.JDG_EQ `$ _ <: _ => S.VAL
     | O.MONO O.JDG_CEQ `$ _ <: _ => S.VAL
     | O.MONO O.JDG_EQ_TYPE `$ _ <: _ => S.VAL
     | O.MONO O.JDG_TRUE `$ _ <: _ => S.VAL
     | O.MONO O.JDG_SYNTH `$ _ <: _ => S.VAL

     (* custom operators *)

     | (O.POLY (O.CUST (opid, ps, _(*ar*)))) `$ args <: env =>
         let
           val entry as {state,...} = Sig.lookup sign opid
           val term = Sig.extract state
           val (mrho, srho) = Sig.applyCustomOperator entry (List.map #1 ps) args
           val term' = substMetaenv mrho term
           val env' = {params = SymEnvUtil.union (#params env, srho), terms = #terms env}
         in
           S.STEP @@ term' <: env'
         end

     | th `$ es <: _ => raise E.error [Fpp.text "Machine encountered unrecognized term", TermPrinter.ppTerm (th $$ es)]

  (* [cut] tells the machine how to plug a value into a hole in a stack frame. As a rule of thumb,
   * any time you return [CUT] in the [step] judgment, you should add a corresponding rule to [cut]. *)
  fun cut _(*sign*) =
    fn (O.MONO O.AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ O.MONO O.LAM `$ [(_,[x]) \ mx] <: env) => mx <: Cl.insertVar env x cl
     | (O.MONO O.FST `$ [_ \ S.HOLE], _ \ O.MONO O.PAIR `$ [_ \ m, _ \ _] <: env) => m <: env
     | (O.MONO O.SND `$ [_ \ S.HOLE], _ \ O.MONO O.PAIR `$ [_ \ _, _ \ n] <: env) => n <: env

     | (O.MONO O.IF `$ [_, _ \ S.HOLE, _ \ S.% cl, _], _ \ O.MONO O.TRUE `$ _ <: _) => cl
     | (O.MONO O.IF `$ [_, _ \ S.HOLE, _, _ \ S.% cl], _ \ O.MONO O.FALSE `$ _ <: _) => cl
     | (O.MONO O.IF `$ [(_,[x]) \ S.% cx, _ \ S.HOLE, _ \ S.% t, _ \ S.% f],
        _ \ O.POLY (O.FCOM (dir, eqs)) `$ (_ \ cap) :: tubes <: env) =>
         let
           (* todo: maybe create a larger closure instead of forcing? *)
           val cx' = Cl.force cx
           val t' = Cl.force t
           val f' = Cl.force f

           val v = Sym.named "v"
           val hv = Syn.intoFcom ((#1 dir, P.ret v), eqs) (cap, tubes)
           val chv = substVar (hv, x) cx'
           fun mkIf m = Syn.into @@ Syn.IF ((x, cx'), m, (t', f'))
         in
           Syn.intoCom (dir, eqs) ((v, chv), mkIf cap, List.map (mapBind mkIf) tubes) <: env
         end

     | (O.MONO O.S_IF `$ [_ \ S.HOLE, _ \ S.% t, _ \ S.% _], _ \ O.MONO O.TRUE `$ _ <: _) => t
     | (O.MONO O.S_IF `$ [_ \ S.HOLE, _ \ S.% _, _ \ S.% f], _ \ O.MONO O.FALSE `$ _ <: _) => f

     | (O.MONO O.S1_ELIM `$ [(_,[_]) \ S.% _, _ \ S.HOLE, _ \ S.% b, ([_],_) \ S.% _], _ \ O.MONO O.BASE `$ _ <: _) => b
     | (O.MONO O.S1_ELIM `$ [(_,[_]) \ S.% _, _ \ S.HOLE, _ \ S.% _, ([u],_) \ S.% (l <: envL)],
       _ \ O.POLY (O.LOOP r) `$ _ <: env) =>
         let
           val r' = Cl.forceParam (r <: env)
         in
           l <: Cl.insertSym envL u r'
         end
     | (O.MONO O.S1_ELIM `$ [(_,[x]) \ S.% cx, _ \ S.HOLE, _ \ S.% b, ([u],_) \ S.% l],
        _ \ O.POLY (O.FCOM (dir, eqs)) `$ (_ \ cap) :: tubes <: env) =>
         let
           (* todo: maybe create a larger closure instead of forcing? *)
           val cx' = Cl.force cx
           val b' = Cl.force b
           val l' = Cl.force l

           val v = Sym.named "v"
           val hv = O.POLY (O.FCOM ((#1 dir, P.ret v), eqs)) $$ (([],[]) \ cap) :: tubes
           val chv = substVar (hv, x) cx'
           fun mkElim m = Syn.into @@ Syn.S1_ELIM ((x, cx'), m, (b', (u, l')))
         in
           Syn.intoCom (dir, eqs) ((v, chv), mkElim cap, List.map (mapBind mkElim) tubes) <: env
         end


     | (O.POLY (O.PATH_AP r) `$ [_ \ S.HOLE], _ \ O.MONO O.PATH_ABS `$ [([u],_) \ m] <: env) =>
         m <: Cl.insertSym env u r

     | (O.POLY (O.HCOM (dir, eqs)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.BOOL `$ _ <: env) =>
         Syn.intoFcom' (dir, eqs) (forceSList args) <: env

     | (O.POLY (O.HCOM _) `$ ((_ \ S.HOLE) :: (_ \ S.% cap) :: _), _ \ O.MONO O.S_BOOL `$ _ <: _) =>
         cap

     | (O.POLY (O.HCOM (dir, eqs)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.S1 `$ _ <: env) =>
         Syn.intoFcom' (dir, eqs) (forceSList args) <: env

     | (O.POLY (O.HCOM (dir, eqs)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.DFUN `$ [_, ((_,[x]) \ bx)] <: env) =>
         let
           val args = forceSList args
           fun apx m = Syn.intoAp (m, Abt.check (`x, O.EXP))
           val hcomx = Syn.intoHcom' (dir, eqs) (bx, List.map (mapBind apx) args)
         in
           Syn.intoLam (x, hcomx) <: env
         end

     | (O.POLY (O.HCOM (dir, eqs)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.DPROD `$ [(_ \ a), ((_,[x]) \ bx)] <: env) =>
         let
           val (_ \ cap) :: tubes = forceSList args
           fun hcom1 r = Syn.intoHcom ((#1 dir, r), eqs)
             (a, Syn.intoFst cap, List.map (mapBind Syn.intoFst) tubes)

           val v = Sym.named "v"
           val com = Syn.intoCom (dir, eqs)
             ( (v, substVar (hcom1 (P.ret v), x) bx)
             , Syn.intoSnd cap, List.map (mapBind Syn.intoSnd) tubes)
         in
           Syn.intoPair (hcom1 (#2 dir), com) <: env
         end

     | (O.POLY (O.HCOM (dir, eqs)) `$ ((_ \ S.HOLE) :: args), _ \ O.MONO O.PATH_TY `$ [(([u],_) \ a), (_ \ p0), (_ \ p1)] <: env) =>
         let
           val (_ \ cap) :: tubes = forceSList args
           fun ap m = Syn.into @@ Syn.PATH_AP (m, P.ret u)
           val eqs = eqs @ equationPair u
           val w = Sym.named "w"
           val tubes = List.map (mapBind ap) tubes @ [([w],[]) \ p0, ([w],[]) \ p1]
           val path = Syn.into @@ Syn.PATH_ABS (u, Syn.intoHcom (dir, eqs) (a, ap cap, tubes))
         in
           path <: env
         end

     | (O.POLY (O.COE _) `$ [_ \ S.HOLE, _\ S.% cl], ([_],_) \ O.MONO O.BOOL `$ _ <: _) => cl
     | (O.POLY (O.COE _) `$ [_ \ S.HOLE, _\ S.% cl], ([_],_) \ O.MONO O.S_BOOL `$ _ <: _) => cl
     | (O.POLY (O.COE _) `$ [_ \ S.HOLE, _\ S.% cl], ([_],_) \ O.MONO O.S1 `$ _ <: _) => cl

     | (O.POLY (O.COE (dir as (r, r'))) `$ [_ \ S.HOLE, _\ S.% cl], ([u],_) \ O.MONO O.DFUN `$ [_\ a, (_,[x]) \ bx] <: env) =>
         let
           fun coea v = Syn.intoCoe (r', v) ((u, a), check (`x, O.EXP))
           val bcoe = substVar (coea (P.ret u), x) bx
           val app = Syn.intoAp (Cl.force cl, coea r)
           val coeR = Syn.intoCoe dir ((u, bcoe), app)
         in
           Syn.intoLam (x, coeR) <: env
         end

     | (O.POLY (O.COE (dir as (r, r'))) `$ [_ \ S.HOLE, _\ S.% cl], ([u],_) \ O.MONO O.DPROD `$ [_\ a, (_,[x]) \ bx] <: env) =>
         let
           val m = Cl.force cl
           fun coe1 v = Syn.intoCoe (r, v) ((u, a), Syn.intoFst m)
           val coe2 = Syn.intoCoe dir ((u, substVar (coe1 (P.ret u), x) bx), Syn.intoSnd m)
         in
           Syn.intoPair (coe1 r', coe2) <: env
         end

     | (O.POLY (O.COE dir) `$ [_ \ S.HOLE, _\ S.% cl], ([u],_) \ O.MONO O.PATH_TY `$ [([v],_) \ a, _ \ p0, _ \ p1] <: env) =>
         let
           val m = Cl.force cl
           val com = Syn.intoCom (dir, equationPair v)
             ((u, a), (Syn.into @@ Syn.PATH_AP (m, P.ret u)), [(([u],[]) \ p0), (([u],[]) \ p1)])
           val path = Syn.into @@ Syn.PATH_ABS (v, com)
         in
           path <: env
         end

     | _ => raise InvalidCut
end

(* From the above definitions, we are able to generate a complete machine implementation,
 * which deals with all the bureaucratic aspects of computation: variables, congruence
 * rules, etc. The supremacy of Standard ML in action! *)
 functor RedPrlMachine (Sig : MINI_SIGNATURE) = AbtMachineUtil (AbtMachine (RedPrlMachineBasis (Sig)))
