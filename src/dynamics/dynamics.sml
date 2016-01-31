structure Dynamics : DYNAMICS =
struct
  structure Abt = Abt
  structure SmallStep = SmallStep
  structure Signature = AbtSignature
  structure Env = Abt.VarCtx

  type abt = Abt.abt
  type 'a step = 'a SmallStep.t
  type sign = Signature.sign
  type 'a env = 'a Abt.VarCtx.dict

  open SmallStep

  datatype 'a closure = <: of 'a * 'a closure env
  infix <:

  exception STUCK of abt

  structure T = Signature.Telescope
  open Abt OperatorData
  infix $ \

  exception hole
  fun ?x = raise x

  structure Pattern = Pattern (Abt)
  structure RewriteRule = RewriteRule (structure Abt = Abt and Pattern = Pattern)

  fun patternFromDef (opid, arity) (def : Signature.def) : Pattern.pattern =
    let
      open Pattern infix $@
      val {parameters, arguments, ...} = def
      val theta = CUST (opid, parameters, arity)
    in
      into (theta $@ List.map (fn (x,_) => MVAR x) arguments)
    end

  fun rewriteRuleFromDef (opid, arity) (def : Signature.def) : RewriteRule.rule =
    let
      open RewriteRule infix ~>
      val {definiens,...} = def
      val pattern = patternFromDef (opid, arity) def
    in
      into (pattern ~> definiens)
    end

  fun stepCust sign (opid, params, arity) (m <: rho) =
    let
      val def = Signature.undef (T.lookup sign opid)
      val rule = rewriteRuleFromDef (opid, arity) def
      val compiled = RewriteRule.compile rule
    in
      ret (RewriteRule.compile rule m <: rho)
    end

  fun step sign (m <: rho) : abt closure step =
    case out m of
         `x => ret (Env.lookup rho x)
       | CUST (opid, params, arity) $ args =>
           stepCust sign (opid, params, arity) (m <: rho)
       | _ => ?hole

end
