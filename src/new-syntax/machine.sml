functor RedPrlMachineBasis (Sig : MINI_SIGNATURE) : ABT_MACHINE_BASIS =
struct
  structure Cl = AbtClosureUtil (AbtClosure (RedPrlAbt))
  structure S = AbtMachineState (Cl)
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  type sign = Sig.sign

  exception InvalidCut

  open RedPrlAbt Cl
  infix 0 \
  infix 1 <:
  infix 2 $ `$ $$ $#

  fun @@ (f, x) = f x
  infixr @@

  structure O = RedPrlOpData

  structure ListUtil =
  struct
    fun indexSatisfyingPredicate p =
      let
        exception NotFound
        fun go i [] = raise NotFound
          | go i (x :: xs) = if p x then i else go (i + 1) xs
      in
        fn xs => SOME (go 0 xs) handle _ => NONE
      end
  end

  fun readParam {params,terms} =
    P.bind (Sym.Ctx.lookup params)

  (* E ⊨ r generic *)
  fun isGeneric env r =
    case readParam env r of
       P.VAR _ => true
     | _ => false

  (* E ⊨ r concrete *)
  fun isConcrete env r =
    case readParam env r of
       P.APP _ => true
     | _ => false

  (* E ⊨ r # r' *)
  fun paramsApart env (r1, r2) =
    not (P.eq Sym.eq (readParam env r1, readParam env r2))

  fun reverseDir (r1, r2) = (r2, r1)

  (* computation rules for Kan compositions at base type *)
  fun stepAtomicHcom exts (r, r') (_ \ cap) tubes env =
    case ListUtil.indexSatisfyingPredicate (isConcrete env) exts of
       SOME i =>
         let
           val ([y],_) \ tube = List.nth (tubes, i)
         in
           S.STEP @@ tube <: Cl.insertSym env y r'
         end
     | NONE =>
         if paramsApart env (r,r') then
           S.VAL
         else
           S.STEP @@ cap <: env

  (* [step] tells our machine how to proceed when computing a term: is it a value,
   * can it step without inspecting the values of its arguments, or does it need to inspect one
   * of its arguments (i.e. it is a cut)? *)
  fun step sign =
    fn O.MONO O.DFUN `$ _ <: _ => S.VAL
     | O.MONO O.FUN `$ [_ \ a, _ \ b] <: env =>
         S.STEP
           @@ O.MONO O.DFUN $$ [([],[]) \ a, ([],[Var.named "_"]) \ b]
           <: env
     | O.MONO O.LAM `$ _ <: _ => S.VAL
     | O.MONO O.AP `$ [_ \ m, _ \ n] <: env =>
         S.CUT
           @@ (O.MONO O.AP `$ [([],[]) \ S.HOLE, ([],[]) \ S.% n], m)
           <: env

     | O.MONO O.BOOL `$ _ <: _ => S.VAL
     | O.MONO O.TRUE `$ _ <: _ => S.VAL
     | O.MONO O.FALSE `$ _ <: _ => S.VAL

     | O.MONO O.S1 `$ _ <: _ => S.VAL
     | O.MONO O.BASE `$ _ <: _ => S.VAL
     | O.POLY (O.LOOP r) `$ _ <: env =>
         (case readParam env r of
             P.VAR a => S.VAL
           | P.APP P.DIM0 => S.STEP @@ O.MONO O.BASE $$ [] <: env
           | P.APP P.DIM1 => S.STEP @@ O.MONO O.BASE $$ [] <: env
           | P.APP _ => raise Match)


     | O.MONO O.AX `$ _ <: _ => S.VAL
     | O.MONO (O.REFINE _) `$ _ <: _ => S.VAL
     | O.MONO (O.EXTRACT tau) `$ [_ \ thm] <: env =>
         S.CUT
           @@ (O.MONO (O.EXTRACT tau) `$ [([],[]) \ S.HOLE], thm)
           <: env

     | O.MONO (O.TAC_SEQ _) `$ _ <: _ => S.VAL
     | O.MONO O.RULE_ID `$ _ <: _ => S.VAL
     | O.MONO O.MTAC_ALL `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_EACH n) `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_FOCUS i) `$ _ <: _ => S.VAL

     | O.MONO O.JDG_EQ `$ _ <: _ => S.VAL
     | O.MONO O.JDG_CEQ `$ _ <: _ => S.VAL
     | O.MONO O.JDG_MEM `$ _ <: _ => S.VAL
     | O.MONO O.JDG_TRUE `$ _ <: _ => S.VAL
     | O.MONO O.JDG_SYNTH `$ _ <: _ => S.VAL

     | O.POLY (O.UNIV _) `$ _ <: _ => S.VAL

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
           val lam = O.MONO O.LAM $$ [([],[x]) \ hcomx]
         in
           S.STEP @@ lam <: env
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

     | _ => raise Match

  (* [cut] tells the machine how to plug a value into a hole in a stack frame. As a rule of thumb,
   * any time you return [CUT] in the [step] judgment, you should add a corresponding rule to [cut]. *)
  fun cut sign =
    fn (O.MONO O.AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ O.MONO O.LAM `$ [(_,[x]) \ mx] <: env) => mx <: Cl.insertVar env x cl
     | (O.MONO (O.EXTRACT _) `$ [_ \ S.HOLE], _ \ O.MONO (O.REFINE (true, _)) `$ [_, _, _ \ m] <: env) => m <: env
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

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.BOOL `$ _ <: env) =>
         O.POLY (O.COE (O.TAG_BOOL, dir)) $$ [([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.S1 `$ _ <: env) =>
         O.POLY (O.COE (O.TAG_S1, dir)) $$ [([],[]) \ Cl.force cl] <: env

     | (O.POLY (O.COE (O.TAG_NONE, dir)) `$ [_ \ S.HOLE, _\ S.% cl] , ([u],_) \ O.MONO O.DFUN `$ [_\ a, (_,[x]) \ bx] <: env) =>
         O.POLY (O.COE (O.TAG_DFUN, dir)) $$ [([u], []) \ a, ([u],[x]) \ bx, ([],[]) \ Cl.force cl] <: env

     | _ => raise InvalidCut
end

(* From the above definitions, we are able to generate a complete machine implementation,
 * which deals with all the bureaucratic aspects of computation: variables, congruence
 * rules, etc. The supremacy of Standard ML in action! *)
 functor RedPrlMachine (Sig : MINI_SIGNATURE) = AbtMachineUtil (AbtMachine (RedPrlMachineBasis (Sig)))
