structure Dynamics : DYNAMICS =
struct
  structure Abt = Abt
  structure SmallStep = SmallStep
  structure Signature = AbtSignature

  type abt = Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign
  type 'a env = 'a Abt.VarCtx.dict

  open SmallStep

  datatype closure = <: of abt * (closure env * Signature.Abt.metaenv)
  infix 2 <:

  exception Stuck of closure

  structure T = Signature.Telescope
  open Abt OperatorData
  infix $ \ $#

  exception hole
  fun ?x = raise x

  fun @@ (f,x) = f x
  infix 0 @@

  local
    structure Pattern = Pattern (Abt)
    structure Unify = AbtLinearUnification (structure Abt = Abt and Pattern = Pattern)

    fun patternFromDef (opid, arity) (def : Signature.def) : Pattern.pattern =
      let
        open Pattern infix 2 $@
        val {parameters, arguments, ...} = def
        val theta = CUST (opid, parameters, arity)
      in
        into @@ theta $@ List.map (fn (x,_) => MVAR x) arguments
      end
  in
    fun stepCust sign (opid, arity) (cl as m <: (rho, mrho)) =
      let
        open Unify infix <*>
        val def = Signature.undef @@ T.lookup sign opid
        val pat = patternFromDef (opid, arity) def
        val (srho, mrho') = unify (pat <*> m)
        val mrho'' = Abt.MetaCtx.union mrho mrho' (fn _ => raise Stuck cl)
        (* todo: do I need to apply srho to the metaenv? *)
      in
        ret @@ Abt.renameEnv srho m <: (rho, mrho'')
      end
  end

  fun step sign (cl as m <: (rho, mrho)) : closure step =
    case out m of
         `x => ret @@ VarCtx.lookup rho x
       | x $# (us, ms) =>
           let
             val (vs', xs) \ m = outb @@ MetaCtx.lookup mrho x
             val srho = List.foldl (fn ((u,v),r) => SymCtx.insert r u v) SymCtx.empty (ListPair.zipEq (vs', us))
             val rho' = List.foldl (fn ((x,m),r) => VarCtx.insert r x (m <: (rho, mrho))) VarCtx.empty (ListPair.zipEq (xs, ms))
             val rho'' = Abt.VarCtx.union rho rho' (fn _ => raise Stuck cl)
             val m' = Abt.renameEnv srho m
           in
             ret @@ m <: (rho'', mrho)
           end
       | CUST (opid, params, arity) $ args =>
           stepCust sign (opid, arity) @@ m <: (rho, mrho)
       | LVL_OP _  $ _ => FINAL
       | LCF _ $ _ => FINAL
       | PROVE $ [_ \ a, _ \ b] => FINAL
       | VEC_LIT _ $ _ => FINAL
       | OP_NONE _ $ _ => FINAL
       | OP_SOME _ $ _ => FINAL
       | _ => ?hole
    handle _ =>
      raise Stuck @@ m <: (rho, mrho)
end
