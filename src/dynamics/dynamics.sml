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

  type vpat = M.Cl.Abt.symbol RedPrlOperator.L.V.t pat
  type kpat = M.Cl.Abt.symbol RedPrlOperator.L.K.t pat
  type dpat = M.Cl.Abt.symbol RedPrlOperator.L.D.t pat

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

  local
    infix 4 `$ $$ <: <|
    infix 3 \
    open O M Abt Cl RedPrlOperators
    structure Ctt = CttOperators
      and Lvl = LevelOperators
      and Syn = RedPrlAbtSyntax

    fun pushV (cl : abt closure, x) (mrho, srho, vrho) =
      (mrho, srho, Var.Ctx.insert vrho x cl)

    fun unquoteV (theta `$ es) =
      V theta $$ es

    fun unquoteK (theta `$ es) =
      K theta $$ es
  in
    (* Plug a value into a continuation *)
    fun plug sign ((v : vpat, k : kpat) <: env) ks =
      case (k, v) of
       (* Lambda application*)
         (CTT_K Ctt.AP `$ [_ \ n], CTT_V Ctt.LAM `$ [(_, [x]) \ mx]) =>
           mx <: pushV (n <: env, x) env <| ks

       (* Lisp-style term introspection; get the domain or codomain of a Pi type *)
       | (CTT_K Ctt.DFUN_DOM `$ _, CTT_V Ctt.DFUN `$ [_ \ a, _]) =>
           a <: env <| ks
       | (CTT_K Ctt.DFUN_COD `$ [_ \ m], CTT_V Ctt.DFUN `$ [_, (_, [x]) \ bx]) =>
           bx <: pushV (m <: env, x) env <| ks

       (* Get the level of a universe*)
       | (CTT_K Ctt.UNIV_GET_LVL `$ _, CTT_V (Ctt.UNIV _) `$ [_ \ i]) =>
           i <: env <| ks

       | (LVL_K Lvl.LSUCC `$ _, LVL_V i `$ _) =>
           Syn.lvl (i + 1) <: env <| ks

       (* Compute the least upper bound / supremum of two universe levels. We compute in two steps. *)
       | (LVL_K Lvl.LSUP0 `$ [_ \ n], LVL_V i `$ _) =>
           let
             val k = K (LVL_K (Lvl.LSUP1 i)) $$ []
           in
             n <: env <| (k <: env) :: ks
           end
       | (LVL_K (Lvl.LSUP1 i) `$ _, LVL_V j `$ _) =>
           Syn.lvl (Int.max (i, j)) <: env <| ks

       | _ => raise Fail "Unhandled cut"

    (* Expand a definitional extension *)
    fun delta sign (d <: env) =
      case d of
         CTT_D Ctt.FUN `$ [_ \ a, _ \ b] => Syn.into (Syn.DFUN (a, Var.named "x", b)) <: env
       | CTT_D Ctt.NOT `$ [_ \ a] => Syn.into (Syn.FUN (a, Syn.into Syn.VOID)) <: env
       | _ => raise Fail "Unhandled definitional extension"
  end
end

structure RedPrlDynamics = LcsDynamics (RedPrlDynamicsBasis)
