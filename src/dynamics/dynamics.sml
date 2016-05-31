structure RedPrlDynamicsBasis : LCS_DYNAMICS_BASIS =
struct
  structure Abt = RedPrlAbt and O = RedPrlOperator
  structure Cl = LcsClosure (Abt)

  structure M = LcsMachine
    (structure Cl = Cl
     open O Cl Abt infix $ $# \ <:

     fun isNeutral (r <: (env as (mrho, srho, vrho))) =
       case out r of
          `x => not (Abt.Var.Ctx.member vrho x)
        | x $# _ => not (Abt.Metavar.Ctx.member mrho x)
        | CUT _ $ [_, _ \ r'] => isNeutral (r' <: env)
        | _ => false

     fun isFinal (m <: env) =
       case out m of
          RET _ $ _ => true
        | _ => isNeutral (m <: env))

  datatype 'o pat = `$ of 'o * M.expr M.Cl.Abt.bview list

  type vpat = M.Cl.Abt.symbol O.L.V.t pat
  type kpat = M.Cl.Abt.symbol O.L.K.t pat
  type dpat = M.Cl.Abt.symbol O.L.D.t pat

  local
    infix `$ $$ \
    open O Abt
  in
    fun unquoteV (theta `$ es) =
      V theta $$ es

    fun unquoteK (theta `$ es) =
      K theta $$ es
  end

  structure Sig =
  struct
    open AbtSignature
    type t = sign
    val empty = Telescope.empty

    fun define sign opid d =
      Telescope.snoc sign opid (def sign d)

    fun lookup sign opid =
      case Telescope.lookup sign opid of
         Decl.DEF d => d
       | _ => raise Fail "no such definitional extension in signature"
  end

  fun plug _ = raise Match
  fun delta _ = raise Match

end

structure RedPrlDynamics = LcsDynamics (RedPrlDynamicsBasis)
