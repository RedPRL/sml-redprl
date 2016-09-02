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

     | _ => raise Match

  fun cut sign =
    fn (AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ O.MONO O.LAM `$ [(_,[x]) \ mx] <: env) => mx <: Cl.insertVar env x cl
     | _ => raise InvalidCut
end
