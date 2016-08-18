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

    type def =
      {parameters : symbols,
       arguments : arguments,
       sort : sort,
       definiens : term}

    type t = sign
    val empty = Telescope.empty

    fun define sign opid {parameters, arguments, sort, definiens} =
      let
        val d' = {parameters = parameters, arguments = arguments, sort = sort, definiens = definiens, pos = NONE}
      in
        Telescope.snoc sign opid (def sign d')
      end

    fun lookup sign opid =
      case Telescope.lookup sign opid of
         Decl.DEF {parameters, arguments, sort, definiens, pos} => {parameters = parameters, arguments = arguments, sort = sort, definiens = definiens}
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

    fun makeTube [] [] = []
      | makeTube (r :: rs) ((([u],_) \ face0) :: (([v],_) \ face1) :: faces) =
          (r, ((u, face0), (v, face1))) :: makeTube rs faces
      | makeTube _ _ = raise Fail "Failed to makeTube"


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
                 val probe = Abt.Sym.fresh (Abt.symctx e) ("probe-" ^ Symbol.toString u)
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

       | (CUB_K (Cub.ID_APP r) `$ [], CUB_V Cub.ID_ABS `$ [([u], _) \ m]) =>
           let
             val mr = Syn.substDim (r, u) m
           in
             mr <: env <| ks
           end

       (* TODO: figure out if we really need to bypass the environment like we're doing here *)
       | (CUB_K (Cub.COE span) `$ [_ \ m <: mEnv], ty) =>
           let
             val u = List.hd us
             val m' = Cl.force (m <: mEnv)

             (* TODO: apply appropriate dimension renamings to 'span'? *)
           in
             case Syn.out (Cl.force (unquoteV ty <: env)) of
                Syn.DFUN (a, x, bx) =>
                  let
                    val xtm = Syn.var (x, SortData.EXP)

                    val coex = Syn.into (Syn.COE ((u, a), DimSpan.new (#ending span, Dim.NAME u), xtm))
                    val bcoe = subst (coex, x) bx
                    val app = Syn.into (Syn.AP (m', coex))
                    val coe = Syn.into (Syn.COE ((u, bcoe), span, app))
                    val lam = Syn.into (Syn.LAM (x, coe))
                  in
                    Cl.new lam |> ks
                  end
              | Syn.ID ((v, a), p1, p2) =>
                  let
                    val app = Syn.into (Syn.ID_APP (m', Dim.NAME v))
                    val tube = [(Dim.NAME v, ((u, p1), (u, p2)))]
                    val com = Syn.heteroCom ((u, a), span, app, tube)
                    val abs = Syn.into (Syn.ID_ABS (v, com))
                  in
                    Cl.new abs |> ks
                  end
              | Syn.BOOL => m <: mEnv <| ks
              | _ => raise Fail "Failed to apply cubical coercion"
           end

       | (CUB_K (Cub.HCOM (extents, span)) `$ ((_ \ cap <: capEnv) :: faces), ty) =>
           let
             val cap' = Cl.force (cap <: capEnv)

             (* Find the first constant (0,1) extent and return the corresponding tube face *)
             val rec findProjectedTubeFace =
               fn [] => NONE
                | (Dim.DIM0, (face0, _)) :: tube => SOME face0
                | (Dim.DIM1, (_, face1)) :: tube => SOME face1
                | _ :: tube => findProjectedTubeFace tube

             val tube = makeTube extents faces
           in
             case Syn.out (Cl.force (unquoteV ty <: env)) of
                Syn.DFUN (a, x, bx) =>
                  let
                    val xtm = Syn.var (x, SortData.EXP)
                    val faces' = List.map (fn (b \ face <: faceEnv) => b \ Syn.into (Syn.AP (Cl.force (face <: faceEnv), xtm))) faces
                    val tube' = makeTube extents faces'
                    val app = Syn.into (Syn.AP (cap', xtm))
                    val hcom = Syn.into (Syn.HCOM (bx, span, app, tube'))
                    val lam = Syn.into (Syn.LAM (x, hcom))
                  in
                    Cl.new lam |> ks
                  end
              | Syn.ID ((u, a), p1, p2) =>
                  let
                    val app = Syn.into (Syn.ID_APP (cap', Dim.NAME u))
                    val faces' = List.map (fn b \ face <: faceEnv => b \ Syn.into (Syn.ID_APP (Cl.force (face <: faceEnv), Dim.NAME u))) faces
                    val tube' =
                      let
                        val w = Symbol.named "_"
                      in
                        makeTube extents faces' @ [(Dim.NAME u, ((w, p1), (w, p2)))]
                      end
                    val hcom = Syn.into (Syn.HCOM (a, span, app, tube'))
                    val abs = Syn.into (Syn.ID_ABS (u, hcom))
                  in
                    Cl.new abs |> ks
                  end
              | Syn.BOOL =>
                  (case findProjectedTubeFace tube of
                      SOME (w, face <: faceEnv) => Syn.substDim (#ending span, w) face <: faceEnv <| ks
                    | NONE =>
                        if Dim.eq Symbol.eq (#starting span, #ending span) then
                          cap <: capEnv <| ks
                        else
                          (* In this case, the syntax abstraction will have represented the hcom as canonical, so we should never
                             step to this state in the machine. *)
                          raise Fail "This case is impossible")
              | _ => raise Fail "Failed to apply kan composition"
           end

       | (CUB_K Cub.BOOL_IF `$ [_, _ \ t, _], CUB_V Cub.BOOL_TT `$ _) => t <| ks
       | (CUB_K Cub.BOOL_IF `$ [_, _, _ \ f], CUB_V Cub.BOOL_FF `$ _) => f <| ks
       | (CUB_K Cub.BOOL_IF `$ [(_,[x]) \ a <: aEnv, _ \ t <: tEnv, _ \ f <: fEnv], CUB_V (Cub.BOOL_HCOM (extents, span)) `$ (_ \ cap) :: faces) =>
           let
             val a' = Cl.force (a <: aEnv)
             val t' = Cl.force (t <: tEnv)
             val f' = Cl.force (f <: fEnv)

             val com =
               let
                 val w = Symbol.new ()
                 val extents' = List.map Dim.NAME extents

                 val hcom =
                   let
                     val span' = DimSpan.new (#starting span, Dim.NAME w)
                     val tube = makeTube extents' faces
                   in
                     Syn.into (Syn.HCOM (Syn.into Syn.BOOL, span', cap, tube))
                   end

                 val a'' = subst (hcom, x) a'
                 fun makeIf m = Syn.into (Syn.BOOL_IF ((x, a'), m, t', f'))
                 val tube = makeTube extents' (List.map (Abt.mapb makeIf) faces)
               in
                 Syn.heteroCom ((w, a''), span, makeIf cap, tube)
               end
           in
             com <: env <| ks
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
