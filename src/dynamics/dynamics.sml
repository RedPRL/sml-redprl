structure Dynamics : DYNAMICS =
struct
  structure Abt = Abt
  structure SmallStep = SmallStep
  structure Signature = AbtSignature

  type abt = Abt.abt
  type abs = Abt.abs
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign

  structure T = Signature.Telescope
  open Abt SmallStep
  infix $ \ $#

  type 'a varenv = 'a Abt.VarCtx.dict
  type 'a metaenv = 'a Signature.Abt.MetaCtx.dict

  datatype 'a closure = <: of 'a * env
  withtype env = abs closure metaenv * symenv * abt closure varenv
  infix 2 <:

  exception Stuck of abt closure


  exception hole
  fun ?x = raise x

  fun @@ (f,x) = f x
  infix 0 @@

  fun <$> (f,x) = SmallStep.map f x
  infix <$>

  fun <#> (x,f) = SmallStep.map f x
  infix <#>

  fun >>= (x,f) = SmallStep.bind f x
  infix >>=


  local
    structure Pattern = Pattern (Abt)
    structure Unify = AbtLinearUnification (structure Abt = Abt and Pattern = Pattern)
    structure SymEnvUtil = ContextUtil (structure Ctx = SymCtx and Elem = Symbol)
    structure AbsEq = struct type t = Abt.abs val eq = Abt.eqAbs end
    open OperatorData

    fun patternFromDef (opid, arity) (def : Signature.def) : Pattern.pattern =
      let
        open Pattern infix 2 $@
        val {parameters, arguments, ...} = def
        val theta = CUST (opid, parameters, arity)
      in
        into @@ theta $@ List.map (fn (x,_) => MVAR x) arguments
      end
  in
    (* computation rules for user-defined operators *)
    fun stepCust sign (opid, arity) (cl as m <: (mrho, srho, rho)) =
      let
        open Unify infix <*>
        val def as {definiens, ...} = Signature.undef @@ T.lookup sign opid
        val pat = patternFromDef (opid, arity) def
        val (srho', mrho') = unify (pat <*> m)
        val srho'' = SymEnvUtil.union (srho, srho') handle _ => raise Stuck cl
        val mrho'' =
          MetaCtx.union mrho
            (MetaCtx.map (fn e => e <: (mrho, srho, rho)) mrho') (* todo: check this? *)
            (fn _ => raise Stuck cl)
      in
        ret @@ definiens <: (mrho'', srho'', rho)
      end
  end

  (* second-order substitution via environments *)
  fun stepMeta x (us, ms) (cl as m <: (mrho, srho, rho)) =
    let
      val e <: (mrho', srho', rho') = MetaCtx.lookup mrho x
      val (vs', xs) \ m = outb e
      val srho'' = ListPair.foldlEq  (fn (u,v,r) => SymCtx.insert r u v) srho' (vs', us)
      val rho'' = ListPair.foldlEq (fn (x,m,r) => VarCtx.insert r x (m <: (mrho', srho', rho'))) rho' (xs, ms)
    in
      ret @@ m <: (mrho', srho'', rho'')
    end

  fun step sign (cl as m <: (mrho, srho, rho)) : abt closure step =
    case out m of
         `x => ret @@ VarCtx.lookup rho x
       | x $# (us, ms) => stepMeta x (us, ms) cl
       | theta $ args =>
           let
             fun f u = SymCtx.lookup srho u handle _ => u
             val theta' = Operator.map f theta
           in
             stepOp sign theta' args (m <: (mrho, srho, rho))
           end
    handle _ =>
      raise Stuck @@ m <: (mrho, srho, rho)

  (* built-in computation rules *)
  and stepOp sign theta args (cl as m <: env) =
    let
      open OperatorData CttOperatorData LevelOperatorData SortData
    in
      case theta $ args of
           CUST (opid, params, arity) $ args =>
             stepCust sign (opid, arity) cl
         | LVL_OP (LBASE _) $ _ => FINAL
         | LVL_OP LSUCC $ [_ \ l] =>
             step sign (l <: env) <#> (fn l' <: env =>
               check (metactx l') (LVL_OP LSUCC $ [([],[]) \ l'], LVL) <: env)
         | LCF theta $ args => FINAL
         | REFINE _ $ _ => FINAL
         | EXTRACT tau $ [_ \ r] =>
             stepExtract sign tau r cl
         | VEC_LIT _ $ _ => FINAL
         | STR_LIT _ $ _ => FINAL
         | OP_NONE _ $ _ => FINAL
         | OP_SOME _ $ _ => FINAL
         | CTT AX $ _ => FINAL
         | CTT (EQ _) $ _ => FINAL
         | CTT (MEMBER tau) $ [_ \ x, _ \ a] =>
             ret @@ check (metactx m) (CTT (EQ tau) $ [([],[]) \ x, ([],[]) \ x, ([],[]) \ a], EXP) <: env
         | CTT UNIV $ [_ \ l] =>
             step sign (l <: env) <#> (fn l' <: env =>
               check (metactx l') (CTT UNIV $ [([],[]) \ l'], EXP) <: env)
         | CTT SQUASH $ _ => FINAL
         | _ => ?hole
    end

  and stepExtract sign tau r (m <: env) =
    let
      open OperatorData SortData
    in
      case step sign (r <: env) of
           FINAL =>
             (case out r of
                  REFINE _ $ [_,_,_\evd] =>
                    (case out evd of
                          OP_SOME _ $ [_ \ evd] => ret @@ evd <: env
                        | _ => raise Stuck (evd <: env))
                | _ => raise Stuck (r <: env))
         | STEP (r' <: env) =>
             ret @@ check' (EXTRACT tau $ [([],[]) \ r'], tau) <: env
    end
end
