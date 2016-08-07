structure RedPrlClosure = LcsClosure (RedPrlAbt)
structure RedPrlMachine = LcsMachine
  (structure Cl = RedPrlClosure and K = RedPrlOperator.L.K
   open RedPrlOperator Cl RedPrlAbt infix $ $# \ <:

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

structure RedPrlDynamicsBasis : LCS_DYNAMICS_BASIS =
struct
  structure Abt = RedPrlAbt and O = RedPrlOperator and M = RedPrlMachine

  type vpat = (M.Cl.Abt.symbol O.L.V.t, M.expr) M.pat
  type kpat = (M.Cl.Abt.symbol O.L.K.t, M.expr M.Cl.closure) M.pat
  type dpat = (M.Cl.Abt.symbol O.L.D.t, M.expr) M.pat

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
    infix 4 `$ $$ <: <| |> ?|>
    infix 3 \
    open O M Abt M.Cl RedPrlOperators
    structure Ctt = CttOperators
      and Lvl = LevelOperators
      and Atm = AtomOperators
      and Rcd = RecordOperators
      and Cub = CubicalOperators
      and Syn = RedPrlAbtSyntax

    fun pushV (cl : abt closure, x) (mrho, srho, vrho) =
      (mrho, srho, Var.Ctx.insert vrho x cl)

    fun unquoteV (theta `$ es) =
      V theta $$ es

    fun unquoteK (theta `$ es) =
      K theta $$ es


    fun symEq env (u, v) =
      let
        val (_, srho, _) = env
        val u' = Sym.Ctx.lookup srho u handle _ => u
        val v' = Sym.Ctx.lookup srho v handle _ => v
      in
        Symbol.eq (u', v')
      end

  in
    (* Plug a value into a continuation *)
    fun plug sign ((us, v <: env), k) ks =
      case (k, v) of

       (* Lambda application *)
         (CTT_K Ctt.AP `$ [_ \ (n <: env')], CTT_V Ctt.LAM `$ [(_, [x]) \ mx]) =>
           mx <: pushV (n <: env', x) env <| ks

       (* Lisp-style term introspection; get the domain or codomain of a Pi type *)
       | (CTT_K Ctt.DFUN_DOM `$ _, CTT_V Ctt.DFUN `$ [_ \ a, _]) =>
           a <: env <| ks
       | (CTT_K Ctt.DFUN_COD `$ [_ \ m <: env'], CTT_V Ctt.DFUN `$ [_, (_, [x]) \ bx]) =>
           bx <: pushV (m <: env', x) env <| ks

       (* Get the level of a universe*)
       | (CTT_K Ctt.UNIV_GET_LVL `$ _, CTT_V (Ctt.UNIV _) `$ [_ \ i]) =>
           i <: env <| ks

       | (CTT_K (Ctt.FRESH (sigma, tau)) `$ [([u], _) \ e <: envE], _) =>
           (case Abt.out e of
               Abt.$ (RET _, [_ \ e']) =>
                 (case Abt.out e' of
                     Abt.$ (theta, es) =>
                       let
                         val supp = support theta
                         fun wrap m = Syn.into (Syn.FRESH (sigma, tau, u, Cl.force (m <: envE)))
                       in
                         if List.exists (fn (v, _) => symEq envE (u, v)) supp then
                           wrap e <: envE <| ks
                         else
                           RET tau $$ [([],[]) \ theta $$ List.map (Abt.mapb wrap) es] <: envE <| ks
                       end
                   | _ => raise Match)
             | _ =>
               let
                 val probe = Abt.Var.fresh (Abt.varctx e) ("probe-" ^ Symbol.toString u)
                 val k = CTT_K (Ctt.FRESH_K ((probe, sigma), tau)) `$ []
                 val (mrho, srho, vrho) = envE
                 val env' = (mrho, Abt.Sym.Ctx.insert srho u probe, vrho)
               in
                 e <: env' <| k :: ks
               end)

       | (CTT_K (Ctt.FRESH_K ((u, sigma), tau)) `$ _, v) =>
           let
             val m = RET tau $$ [([],[]) \ unquoteV v]
             val k = CTT_K (Ctt.FRESH (sigma, tau)) `$ [([u], []) \ m <: env]
           in
             Syn.into Syn.DUMMY <: env <| k :: ks
           end

       (* The level successor operator is eager *)
       | (LVL_K Lvl.LSUCC `$ _, LVL_V i `$ _) =>
           Syn.lvl (i + 1) <: env <| ks

       (* Compute the least upper bound / supremum of two universe levels. We compute in two steps. *)
       | (LVL_K Lvl.LSUP0 `$ [_ \ n <: env'], LVL_V i `$ _) =>
           let
             val k = LVL_K (Lvl.LSUP1 i) `$ []
           in
             n <: env' <| k :: ks
           end
       | (LVL_K (Lvl.LSUP1 i) `$ _, LVL_V j `$ _) =>
           Syn.lvl (Int.max (i, j)) <: env <| ks

       (* Compute an equality test on symbol references / atoms. We do this in two steps, as with level suprema. *)
       | (ATM_K (Atm.TEST0 (sigma, tau)) `$ [_ \ t2, _ \ l, _ \ r], ATM_V (Atm.TOKEN (u, _)) `$ _) =>
           let
             val k = ATM_K (Atm.TEST1 ((u, sigma), tau)) `$ [([],[]) \ l, ([],[]) \ r]
           in
             t2 <| k :: ks
           end
       | (ATM_K (Atm.TEST1 ((u, sigma), tau)) `$ [_ \ l, _ \ r], ATM_V (Atm.TOKEN (v, _)) `$ _) =>
           (if symEq env (u, v) then l else r) <| ks

       (* Compute projection from a record; if the head label matches, return that; otherwise, keep working through the record. *)
       | (RCD_K (Rcd.PROJ lbl) `$ _, RCD_V (Rcd.CONS lbl') `$ [_ \ hd, _ \ tl]) =>
           if symEq env (lbl, lbl') then
             hd <: env <| ks
           else
             tl <: env <| (RCD_K (Rcd.PROJ lbl) `$ []) :: ks

       | (RCD_K (Rcd.PROJ_TY lbl) `$ [_ \ rcd <: env'], RCD_V (Rcd.RECORD lbl') `$ [_ \ a, ([],[x]) \ bx]) =>
           if symEq env (lbl, lbl') then
             a <: env <| ks
           else
             let
               val proj = Syn.into (Syn.RCD_PROJ (lbl', rcd))
             in
               bx <: pushV (proj <: env', x) env <| (RCD_K (Rcd.PROJ_TY lbl) `$ [([],[]) \ rcd <: env']) :: ks
             end

       | (CUB_K Cub.COE `$ [_ \ r <: rEnv, _ \ r' <: r'Env, _ \ m <: mEnv], ty) =>
           let
             val u = List.hd us

             (* TODO: figure out if we really need to bypass the environment like we're doing here *)
             val starting = Cl.force (r <: rEnv)
             val ending = Cl.force (r' <: r'Env)
           in
             case ty of
                CTT_V DFUN `$ [_ \ a, ([x], _) \ bx] =>
                  let
                    val xtm = Syn.var (x, SortData.EXP)

                    val a' = Cl.force (a <: env)
                    val bx' = Cl.force (bx <: env)

                    val coex = Syn.into (Syn.COE ((u, a'), (ending, Syn.into (Syn.DIMREF u)), xtm))
                    val bcoe = subst (coex, x) bx'
                    val app = Syn.into (Syn.AP (Cl.force (m <: mEnv), coex))
                    val coe = Syn.into (Syn.COE ((u, bcoe), (starting, ending), app))
                    val lam = Syn.into (Syn.LAM (x, coe))
                  in
                    Cl.new lam <| ks
                  end
              | _ => raise Fail "Failed to apply cubical coercion"
           end

       | (CUB_K Cub.HCOM `$ [_ \ r <: rEnv, _ \ r' <: r'Env, _ \ cap <: capEnv, _ \ tube <: tubeEnv], ty) =>
           let
             val capDim = Cl.force (r <: rEnv)
             val cmpDim = Cl.force (r' <: r'Env)
             val cap' = Cl.force (cap <: capEnv)
             val tube' = Cl.force (tube <: tubeEnv)
             val slices = Syn.outTubeSlices tube'
           in
             case ty of
                CTT_V DFUN `$ [_ \ a, ([x], _) \ bx] =>
                  let
                    val xtm = Syn.var (x, SortData.EXP)

                    val a' = Cl.force (a <: env)
                    val bx' = Cl.force (bx <: env)

                    val slices' = List.map (fn (extent, (v, n0), (w, n1)) => (extent, (v, Syn.into (Syn.AP (n0, xtm))), (w, Syn.into (Syn.AP (n1, xtm))))) slices
                    val app = Syn.into (Syn.AP (cap', xtm))
                    val hcom = Syn.into (Syn.HCOM (bx', (capDim, cmpDim), app, slices'))
                    val lam = Syn.into (Syn.LAM (x, hcom))
                  in
                    Cl.new lam <| ks
                  end
              | _ => raise Fail "Failed to apply kan composition coercion"
           end

       (* Extract the witness from a refined theorem object. *)
       | (EXTRACT tau `$ _, REFINE _ `$ [_, _, _ \ e]) =>
           let
             val k = FROM_SOME tau `$ []
           in
             e <: env <| k :: ks
           end

       | (FROM_SOME tau `$ _, OP_SOME _ `$ [_ \ e]) =>
           e <: env <| ks

       | (THROW `$ _, EXN a `$ [_ \ e]) =>
           let
             val m = RET SortData.EXP $$ [([],[]) \ unquoteV v]
           in
             m <: env ?|> ks
           end

       | (CATCH _ `$ _, _) =>
           let
             val m = RET SortData.EXP $$ [([],[]) \ unquoteV v]
           in
             m <: env |> ks
           end

       | _ => raise Fail "Unhandled cut"

    fun catch sign (v <: env, k) st =
      case (v, k) of
         (EXN a `$ [_ \ m], CATCH b `$ [(_,[x]) \ nx <: env']) =>
           if symEq env (a, b) then
             SOME (nx <: pushV (m <: env, x) env' <| st)
           else
             NONE
       | _ => NONE

    val throw = Syn.into o Syn.RAISE

    (* Expand a definitional extension *)
    fun delta sign (d <: env) =
      case d of
       (* independent functions are defined in terms of dependent functions *)
         CTT_D Ctt.FUN `$ [_ \ a, _ \ b] => Syn.into (Syn.DFUN (a, Var.named "x", b)) <: env

       (* negation is implication of the empty type *)
       | CTT_D Ctt.NOT `$ [_ \ a] => Syn.into (Syn.FUN (a, Syn.into Syn.VOID)) <: env

       (* membership is reflexive equality *)
       | CTT_D (Ctt.MEMBER tau) `$ [_ \ m, _ \ a] =>
           Syn.into (Syn.EQ (tau, m, m, a)) <: env

       | RCD_D (Rcd.SINGL lbl) `$ [_ \ a] =>
           let
             val x = Var.named "_"
           in
             Syn.into (Syn.RECORD_TY (lbl, a, x, Syn.into Syn.AX)) <: env
           end

       | _ => raise Fail "Unhandled definitional extension"
  end
end

structure RedPrlDynamics = LcsDynamics (RedPrlDynamicsBasis)
