structure RedPrlMachineBasis : ABT_MACHINE_BASIS =
struct
  structure Cl = AbtClosureUtil (AbtClosure (RedPrlAbt))
  structure S = AbtMachineState (Cl)
  structure P = struct open RedPrlParamData RedPrlParameterTerm end
  type sign = Signature.sign

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

  fun isGeneric env r =
    case readParam env r of
       P.VAR _ => true
     | _ => false

  fun isConcrete env r =
    case readParam env r of
       P.APP _ => true
     | _ => false

  fun paramsApart env (r1, r2) =
    not (P.eq Sym.eq (readParam env r1, readParam env r2))

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
     | O.MONO O.CEQ `$ _ <: _ => S.VAL
     | O.MONO (O.REFINE _) `$ _ <: _ => S.VAL
     | O.MONO O.EXTRACT `$ [_ \ thm] <: env =>
         S.CUT
           @@ (O.MONO O.EXTRACT `$ [([],[]) \ S.HOLE], thm)
           <: env

     | O.MONO (O.TAC_SEQ _) `$ _ <: _ => S.VAL
     | O.MONO O.TAC_ID `$ _ <: _ => S.VAL
     | O.MONO O.MTAC_ALL `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_EACH n) `$ _ <: _ => S.VAL
     | O.MONO (O.MTAC_FOCUS i) `$ _ <: _ => S.VAL

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

     | _ => raise Match

  fun cut sign =
    fn (O.MONO O.AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ O.MONO O.LAM `$ [(_,[x]) \ mx] <: env) => mx <: Cl.insertVar env x cl
     | (O.MONO O.EXTRACT `$ [_ \ S.HOLE], _ \ O.MONO (O.REFINE true) `$ [_, _, _ \ m] <: env) => m <: env
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
     | _ => raise InvalidCut
end

structure RedPrlMachine = AbtMachine (RedPrlMachineBasis)
