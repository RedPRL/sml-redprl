functor LcfElaborator (R : REFINER) : LCF_ELABORATOR =
struct
  structure Refiner = R
  structure T = R.Tacticals
  structure Lcf = R.Tacticals.Lcf
  structure MT = Multitacticals (R.Tacticals.Lcf)

  open Abt NominalLcfOperatorData OperatorData SortData
  infix $ $# \

  fun elaborateOpt m =
    case infer m of
         (OP_SOME _ $ [_ \ n], OPT _) => SOME n
       | (OP_NONE _ $ _, OPT _) => NONE
       | _ => raise Fail "Expected SOME or NONE"

  fun elaborateVec m =
    case #1 (infer m) of
         VEC_LIT _ $ es => List.map (fn (_ \ n) => n) es
       | _ => raise Fail "Expected vector argument"

  type env = Refiner.ntactic VarCtx.dict

  fun probe (alpha : R.name_store) : R.name_store * int ref =
    let
      val mref = ref 0
      fun updateModulus i = if !mref < i then mref := i else ()
      fun beta i = (updateModulus (i + 1); alpha i)
    in
      (beta, mref)
    end

  fun prepend us =
    let
      val n = List.length us
    in
      fn alpha => fn i =>
        if i < n then
          List.nth (us, i)
        else
          alpha (i + n)
    end

  fun bite n alpha =
    fn i =>
      alpha (i + n)

  fun evalOpen sign t =
    DynamicsUtil.evalOpen sign t

  fun Rec f alpha jdg =
    f (Rec f) alpha jdg

  structure Tele = R.Tacticals.Lcf.T

  fun Trace m jdg =
    let
      val x = Abt.Metavariable.named "?"
      val psi = Tele.snoc Tele.empty x jdg
    in
      print (ShowAbt.toString m ^ "\n");
      (psi, fn rho => Tele.lookup rho x)
    end

  fun collectSeqs sign rho t =
    case out t of
         LCF (SEQ _) $ [_ \ mt, (us, _) \ t] => (us, mt) :: collectSeqs sign rho t
       | _ => [([], check (metactx t) (LCF ALL $ [([],[]) \ t], MTAC))]

  local
    fun go syms m =
      let
        val (m', tau) = infer m
        val psi = metactx m
      in
        case m' of
           LCF (HYP_VAR a) $ _ =>
             if SymCtx.member syms a then
               m
             else
               check' (`a, EXP)
         | theta $ es =>
             check psi (theta $ List.map (goAbs syms) es, tau)
         | x $# (us, ms) =>
             check psi (x $# (us, List.map (go syms) ms), tau)
         | _ => m
      end
    and goAbs syms ((us,xs) \ m) =
      let
        val syms' = List.foldl (fn (u, acc) => SymCtx.insert acc u ()) syms us
      in
        (us,xs) \ go syms' m
      end
  in
    (* Replace hypothesis-references @u with variables `u; this will *only* expand
     * unbound hyp-refs. *)
   val expandHypVars =
      go SymCtx.empty
  end

  val optionToTarget =
    fn NONE => Target.TARGET_CONCL
     | SOME a => Target.TARGET_HYP a

  fun extendTactic (T : Refiner.ntactic) : Refiner.nmultitactic =
    fn alpha => Lcf.subst (fn _ => T alpha)

  fun contractTactic (M : Refiner.nmultitactic) : Refiner.ntactic =
    fn alpha => fn jdg =>
      let
        val x = Metavariable.named "?x"
        val psi = Tele.snoc Tele.empty x jdg
      in
        M alpha (psi, fn rho => Tele.lookup rho x)
      end

  fun elaborateTactic sign rho t : Refiner.ntactic =
    let
      val (t', tau) = infer (evalOpen sign t handle _ => t)
    in
      case t' of
           LCF ORELSE $ [([],[]) \ t1, ([],[]) \ t2] =>
             let
               val T1 = elaborateStmt sign rho t1
               val T2 = elaborateStmt sign rho t2
             in
               fn alpha => fn jdg =>
                 T1 alpha jdg
                   handle _ => T2 alpha jdg
             end
         | LCF ID $ _ => (fn _ => T.ID)
         | LCF FAIL $ _ => (fn _ => fn _ => raise Fail "Fail")
         | LCF (TRACE _) $ [_ \ m] => (fn _ => Trace m)
         | LCF PROGRESS $ [_ \ t] =>
             T.PROGRESS o elaborateStmt sign rho t
         | LCF (ELIM (target, _)) $ [] =>
             R.Elim target
         | LCF (HYP (target, _)) $ [] =>
             R.Hyp target
         | LCF (UNHIDE (target, _)) $ [] =>
             R.Unhide target
         | LCF (INTRO {rule}) $ [] =>
             R.Intro rule
         | LCF (EQ {rule}) $ [] =>
             R.Eq rule
         | LCF EXT $ [] =>
             R.Ext
         | LCF (CSTEP i) $ [] =>
             R.CStep sign i
         | LCF CSYM $ [] =>
             R.CSym
         | LCF CEVAL $ [] =>
             R.CEval sign
         | LCF (REWRITE_GOAL tau) $ [_ \ m] =>
             R.RewriteGoal m
         | LCF (EVAL_GOAL targ) $ [] =>
             R.EvalGoal sign (optionToTarget targ)
         | LCF (WITNESS tau) $ [_ \ m] =>
             R.Witness m
         | LCF (UNFOLD (opid, targ)) $ [] =>
             R.Unfold sign opid (optionToTarget targ)
         | LCF (NORMALIZE targ) $ [] =>
             R.Normalize sign (optionToTarget targ)
         | LCF AUTO $ [] =>
             R.AutoStep sign
         | LCF REC $ [(_, [x]) \ t] =>
             Rec (fn T => elaborateStmt sign (VarCtx.insert rho x T) t)
         | `x => VarCtx.lookup rho x
         | _ => raise Fail ("Expected tactic, got: " ^ DebugShowAbt.toString t)
    end

  and elaborateMultitactic sign rho m : Refiner.nmultitactic =
    let
      val (m', tau) = infer (evalOpen sign m handle _ => m)
      val _ = case tau of MTAC => () | _ => raise Fail "elaborateMTac called on wrong sort"
    in
      case m' of
           LCF ALL $ [_ \ t] =>
             extendTactic (elaborateStmt sign rho t)
         | LCF EACH $ [_ \ vec] =>
             let
               val Ts = List.map (elaborateStmt sign rho) (elaborateVec (evalOpen sign vec))
             in
               fn alpha =>
                 MT.EACH' (List.map (fn T => T alpha) Ts)
             end
         | LCF (FOCUS i) $ [_ \ t] =>
             MT.FOCUS i o elaborateStmt sign rho t
         | _ => raise Fail "Unrecognized multitactic"
    end

  and elaborateStmt sign rho : abt -> Refiner.ntactic =
    let
      fun go t =
        let
          val (t', tau) = infer (expandHypVars (evalOpen sign t handle _ => t))
          val _ = case tau of TAC => () | _ => raise Fail "elaborateStmt called on wrong sort"
        in
          case t' of
               LCF (SEQ taus) $ [([],[]) \ m, (us, _) \ t] => (us, elaborateMultitactic sign rho m) :: go t
             | _ => [([], extendTactic (elaborateTactic sign rho t))]
        end
    in
      contractTactic
        o List.foldr
            (fn ((us, front : Refiner.nmultitactic), rest : Refiner.nmultitactic) => fn alpha => fn st =>
              let
                val beta = prepend us alpha
                val (beta', modulus) = probe (prepend us beta)
                val st' = front beta' st
              in
                rest (bite (!modulus) beta) st'
              end)
            (fn _ => fn st => st)
        o go
    end

  fun elaborate sign rho t : Refiner.ntactic =
    elaborateStmt sign rho t

  fun elaborate' sign =
    elaborate sign VarCtx.empty
end

structure LcfElaborator = LcfElaborator (Refiner)
