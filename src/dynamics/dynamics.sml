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

  structure SymCtx = Symbol.Ctx and VarCtx = Variable.Ctx and MetaCtx = Metavariable.Ctx

  type 'a varenv = 'a Abt.Variable.Ctx.dict
  type 'a metaenv = 'a Signature.Abt.Metavariable.Ctx.dict

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

  fun asApp m =
    case out m of
       theta $ es => (theta, es)
     | _ => raise Fail "Expected operator"

  val subterms =
    #2 o asApp


  local
    fun listModifyItem n f =
      let
        fun go i =
          fn [] => []
           | y :: ys => (if i = n then f y else y) :: go (i + 1) ys
      in
        go 0
      end
  in
    fun inspectArgument step (m <: env) i k =
      let
        val (theta, es) = asApp m
        val _ \ n = List.nth (es, i)
      in
        case step (n <: env) of
           FINAL =>
             (case out n of
                 view as (theta' $ es') => k view
               | _ => raise Fail "Expected operator")
         | STEP (n' <: env') =>
             STEP @@
               check
                 (theta $ listModifyItem i (fn (us, xs) \ a => (us,xs) \ n') es,
                  sort m)
               <: env'
      end
  end

  fun compareSymbols env (u, v) =
    let
      val (_, srho, _) = env
      val u' = SymCtx.lookup srho u handle _ => u
      val v' = SymCtx.lookup srho v handle _ => v
    in
      Symbol.eq (u', v')
    end

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
    fun stepCust sign (opid, arity) (cl as m <: (mrho, srho, vrho)) =
      let
        open Unify infix <*>
        val def as {definiens, ...} =
          case T.lookup sign opid of
             Signature.Decl.DEF d => d
           | _ => raise Fail "Expected DEF"
        val pat = patternFromDef (opid, arity) def
        val (srho', mrho') = unify (pat <*> m)
        val srho'' = SymEnvUtil.union (srho, srho') handle _ => raise Stuck cl
        val mrho'' =
          MetaCtx.union mrho
            (MetaCtx.map (fn e => e <: (mrho, srho, vrho)) mrho')
            (fn _ => raise Stuck cl)
      in
        ret @@ definiens <: (mrho'', srho'', vrho)
      end
  end

  (* second-order substitution via environments *)
  fun stepMeta x (us, ms) (cl as m <: (mrho, srho, vrho)) =
    let
      val e <: (mrho', srho', vrho') = MetaCtx.lookup mrho x
      val (vs', xs) \ m = outb e
      val srho'' = ListPair.foldlEq  (fn (v,(u, _),r) => SymCtx.insert r v u) srho' (vs', us)
      val vrho'' = ListPair.foldlEq (fn (x,m,r) => VarCtx.insert r x (m <: (mrho', srho', vrho'))) vrho' (xs, ms)
    in
      ret @@ m <: (mrho', srho'', vrho'')
    end

  fun step sign (cl as m <: (mrho, srho, vrho)) : abt closure step =
    case out m of
       `x => ret @@ VarCtx.lookup vrho x
     | x $# (us, ms) => stepMeta x (us, ms) cl
     | theta $ args =>
         let
           fun f u = SymCtx.lookup srho u handle _ => u
           val theta' = Operator.map f theta
         in
           stepOp sign theta' args (m <: (mrho, srho, vrho))
         end

  (* built-in computation rules *)
  and stepOp sign theta args (cl as m <: env) =
    let
      open OperatorData CttOperatorData LevelOperatorData AtomsOperatorData SortData RecordOperatorData
    in
      case theta $ args of
         CUST (opid, params, arity) $ args =>
           stepCust sign (opid, arity) cl
       | LVL_OP LBASE $ _ => FINAL
       | LVL_OP LSUCC $ [_ \ l] => FINAL
       | LVL_OP LSUP $ _ =>
           stepLvlSup sign (m <: env)
       | LCF _ $ _ => FINAL
       | RCD (PROJ lbl) $ _ =>
           stepRcdProj sign lbl (m <: env)
       | RCD SINGL_GET_TY $ _ =>
           stepRcdSinglGetTy sign (m <: env)
       | RCD (RECORD lbl) $ _ =>
           stepRcdRecord sign lbl (m <: env)
       | RCD _ $ _ => FINAL
       | REFINE _ $ _ => FINAL
       | EXTRACT tau $ [_ \ r] =>
           stepExtract sign tau r cl
       | VEC_LIT _ $ _ => FINAL
       | STR_LIT _ $ _ => FINAL
       | OP_NONE _ $ _ => FINAL
       | OP_SOME _ $ _ => FINAL
       | CTT AX $ _ => FINAL
       | CTT (EQ _) $ _ => FINAL
       | CTT (CEQUIV _) $ _ => FINAL
       | CTT (MEMBER tau) $ [_ \ x, _ \ a] =>
           ret @@ check (CTT (EQ tau) $ [([],[]) \ x, ([],[]) \ x, ([],[]) \ a], EXP) <: env
       | CTT (UNIV tau) $ [_ \ l] => FINAL
       | CTT (SQUASH _) $ _ => FINAL
       | CTT (ENSEMBLE _) $ _ => FINAL
       | CTT (BASE _) $ _ => FINAL
       | CTT (TOP _) $ _ => FINAL
       | CTT DFUN $ _ => FINAL
       | CTT DEP_ISECT $ _ => FINAL
       | CTT FUN $ [_ \ a, _ \ b] =>
           ret @@ check (CTT DFUN $ [([],[]) \ a, ([],[Variable.named "x"]) \ b], EXP) <: env
       | CTT LAM $ _ => FINAL
       | CTT AP $ _ =>
           stepAp sign (m <: env)
       | CTT VOID $ [] => FINAL
       | CTT NOT $ [_ \ a] =>
           let
             val void = check (CTT VOID $ [], EXP)
           in
             ret @@ check (CTT FUN $ [([],[]) \ a, ([],[]) \ void], EXP) <: env
           end
       | CTT DFUN_DOM $ _ =>
           stepDFunDom sign (m <: env)
       | CTT DFUN_COD $ _ =>
           stepDFunCod sign (m <: env)
       | CTT UNIV_GET_LVL $ _ =>
           stepUnivGetLvl sign (m <: env)
       | CTT (NU _) $ _ =>
           stepNu sign (m <: env)
       | ATM (ATOM _) $ _ => FINAL
       | ATM (TOKEN _) $ _ => FINAL
       | ATM (TEST _) $ _ =>
           stepAtomTest sign (m <: env)
       | _ => ?hole
    end

  and stepAp sign (ap <: env) =
    let
      open OperatorData CttOperatorData SortData
    in
      inspectArgument (step sign) (ap <: env) 0
        (fn CTT LAM $ [(_,[x]) \ mx] =>
              let
                val _ \ n = List.nth (subterms ap, 1)
                val (mrho, srho, vrho) = env
              in
                ret @@ mx <: (mrho, srho, VarCtx.insert vrho x (n <: env))
              end
          | _ => raise Stuck (ap <: env))
    end

  and stepDFunDom sign (dom <: env) =
    let
      open OperatorData CttOperatorData SortData
    in
      inspectArgument (step sign) (dom <: env) 0
        (fn CTT DFUN $ [_ \ a, _] => ret @@ a <: env
          | _ => raise Stuck @@ dom <: env)
    end

  and stepDFunCod sign (cod <: env) =
    let
      open OperatorData CttOperatorData SortData
    in
      inspectArgument (step sign) (cod <: env) 0
        (fn CTT DFUN $ [_ \ _, (_, [x]) \ bx] =>
              let
                val _ \ n = List.nth (subterms cod, 1)
                val (mrho, srho, vrho) = env
              in
                ret @@ bx <: (mrho, srho, VarCtx.insert vrho x (n <: env))
              end
          | _ => raise Stuck @@ cod <: env)
    end

  and stepUnivGetLvl sign (getLvl <: env) =
    let
      open OperatorData CttOperatorData SortData
    in
      inspectArgument (step sign) (getLvl <: env) 0
        (fn CTT (UNIV tau) $ [_ \ lvl] => ret @@ lvl <: env
          | _ => raise Stuck @@ getLvl <: env)
    end

  and stepLvlSup sign (m <: env) =
    let
      open OperatorData LevelOperatorData SortData
      val psi = metactx m
      fun makeSup x y = check (LVL_OP LSUP $ [([],[]) \ x, ([],[]) \ y], LVL)
      fun makeSucc x = check (LVL_OP LSUCC $ [([],[]) \ x], LVL)
      val _ \ l1 = List.nth (subterms m, 0)
      val _ \ l2 = List.nth (subterms m, 1)
    in
      case step sign (l1 <: env) of
         FINAL =>
           (case step sign (l2 <: env) of
               FINAL =>
                 (case (out l1, out l2) of
                     (LVL_OP LSUCC $ _, LVL_OP LBASE $ _) => ret @@ l1 <: env
                   | (LVL_OP LSUCC $ [_ \ l3], LVL_OP LSUCC $ [_ \ l4]) => ret @@ makeSucc (makeSup l3 l4) <: env
                   | (LVL_OP LBASE $ _, LVL_OP LBASE $ _) => ret @@ l1 <: env
                   | (LVL_OP LBASE $ _, LVL_OP LSUCC $ _) => ret @@ l2 <: env
                   | _ => raise Stuck (m <: env))
             | STEP (l2' <: env) => ret @@ makeSup l1 l2' <: env)
       | STEP (l1' <: env) => ret @@ makeSup l1' l2 <: env
    end

  and stepRcdProj sign lbl (proj <: env) =
    let
      open OperatorData RecordOperatorData SortData
    in
      inspectArgument (step sign) (proj <: env) 0
        (fn RCD (CONS lbl') $ [_ \ hd, _ \ tl] =>
              if compareSymbols env (lbl, lbl') then
                ret @@ hd <: env
              else
                ret @@ check (RCD (PROJ lbl) $ [([],[]) \ tl], EXP) <: env
          | _ => raise Stuck @@ proj <: env)
    end

  and stepRcdSinglGetTy sign (proj <: env) =
    let
      open OperatorData RecordOperatorData SortData
    in
      inspectArgument (step sign) (proj <: env) 0
        (fn RCD (SINGL _) $ [_ \ a] => ret @@ a <: env
          | _ => raise Stuck @@ proj <: env)
    end

  and stepRcdRecord sign lbl (rcd <: env) =
    let
      open OperatorData CttOperatorData RecordOperatorData SortData
    in
      case out rcd of
         RCD (RECORD lbl) $ [_ \ a , (_, [x]) \ bx] =>
           let
             val psi = metactx rcd
             fun depIsect a x bx = check (CTT DEP_ISECT $ [([],[]) \ a, ([],[x]) \ bx], EXP)
             val singl = check (RCD (SINGL lbl) $ [([],[]) \ a], EXP)
             val self = Variable.named "self"
             val proj = check (RCD (PROJ lbl) $ [([],[]) \ check (`self, EXP)], EXP)
             val bself = subst (proj, x) bx
           in
             ret @@ depIsect singl self bself <: env
           end
       | _ => raise Stuck @@ rcd <: env
    end

  and stepAtomTest sign (m <: env) =
    let
      open OperatorData AtomsOperatorData SortData
      val es = subterms m
      val _ \ yes = List.nth (es, 2)
      val _ \ no = List.nth (es, 3)
    in
      inspectArgument (step sign) (m <: env) 0
        (fn ATM (TOKEN (u1, _)) $ _ =>
              inspectArgument (step sign) (m <: env) 1
                (fn ATM (TOKEN (u2, _)) $ _ =>
                      ret @@ (if compareSymbols env (u1, u2) then yes else no) <: env
                  | _ => raise Stuck @@ m <: env)
          | _ => raise Stuck @@ m <: env)
    end

  and stepExtract sign tau r (m <: env) =
    let
      open OperatorData SortData
    in
      inspectArgument (step sign) (m <: env) 0
        (fn REFINE _ $ [_, _, _ \ evd] =>
              (case out evd of
                  OP_SOME _ $ [_ \ evd] => ret @@ evd <: env
                | _ => raise Stuck (evd <: env))
          | _ => raise Stuck @@ m <: env)
    end

  and stepNu sign (m <: env) =
    let
      open OperatorData CttOperatorData
    in
      case out m of
         CTT (NU (sigma, tau)) $ [([u], _) \ t] =>
           (case step sign (t <: env) of
               FINAL =>
                 (case out t of
                     theta $ _ =>
                       let
                         val us = Operator.support theta
                       in
                         (* If the symbol is part of the support of the head operator, then
                          * we cannot proceed; otherwise, the symbol generation is pushed down
                          * into the subterms of the operator. *)
                         if List.exists (fn (v, _) => compareSymbols env (u, v)) us then
                           ret @@ m <: env
                         else
                           ret @@ pushDownNu (sigma, tau) env u t <: env
                       end
                   | _ => ret @@ pushDownNu (sigma, tau) env u t <: env)
             | STEP t' =>
                 let
                   (* If t was non-canonical, try computing it with a fresh variable 'a' and then
                    * re-embed the result in the nu-expression, replacing 'a' in the result with 'u'. *)
                   val (mrho, srho, vrho) = env
                   val a = Symbol.named "a"
                   val srho' = SymCtx.insert srho u a
                   val env' = (mrho, srho', vrho)
                 in
                   case step sign (t <: env') of
                      FINAL =>
                        let
                          val (mrho', srho'', vrho') = env'
                          val srho''' = SymCtx.insert srho a u
                          val env''' = (mrho', srho''', vrho')
                        in
                          ret @@ check (CTT (NU (sigma, tau)) $ [([u], []) \ t], tau) <: env'''
                        end
                    | STEP (t' <: env'') =>
                        let
                          val (mrho', srho'', vrho') = env''
                          val srho''' = SymCtx.insert srho a u
                          val env''' = (mrho', srho''', vrho')
                        in
                          ret @@ check (CTT (NU (sigma, tau)) $ [([u], []) \ t'], tau) <: env'''
                        end
                 end)
       | _ => raise Stuck @@ m <: env
    end

  and pushDownNu (sigma, tau) env u m =
    case infer m of
       (theta $ es, tau) =>
         check (theta $ List.map (pushDownNuB (sigma, tau) env u) es, tau)
     | _ => raise Fail "Impossible"

  and pushDownNuB (sigma, tau) env u ((us, xs) \ m) =
    let
      open OperatorData CttOperatorData
    in
      (us, xs) \ check (CTT (NU (sigma, tau)) $ [([u], []) \ m], tau)
    end
end
