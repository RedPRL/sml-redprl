functor LcfElaborator (R : REFINER) : LCF_ELABORATOR =
struct
  structure Refiner = R
  structure T = R.Tacticals
  structure MT = Multitacticals (R.Tacticals.Lcf)

  open Abt NominalLcfOperatorData OperatorData SortData
  infix $ \

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
      val psi = Tele.snoc Tele.empty (x, jdg)
    in
      print (ShowAbt.toString m ^ "\n");
      (psi, fn rho => Tele.lookup rho x)
    end

  fun collectSeqs sign rho t =
    case out t of
         LCF (SEQ _) $ [_ \ mt, (us, _) \ t] => (us, mt) :: collectSeqs sign rho t
       | _ => [([], check (metactx t) (LCF ALL $ [([],[]) \ t], MTAC))]

  fun elaborate sign rho t : Refiner.ntactic =
    let
      val t' = evalOpen sign t handle _ => t
    in
      case out t' of
           LCF (SEQ _) $ _ => foldl (fn (t, T) => elaborateM sign rho T t) (fn _ => T.ID) (collectSeqs sign rho t')
         | LCF ID $ _ => (fn _ => T.ID)
         | LCF FAIL $ _ => (fn _ => fn _ => raise Fail "Fail")
         | LCF (TRACE _) $ [_ \ m] => (fn _ => Trace m)
         | LCF ORELSE $ [_ \ t1, _ \ t2] =>
             let
               val T1 = elaborate sign rho t1
               val T2 = elaborate sign rho t2
             in
               fn alpha =>
                 T.ORELSE (T1 alpha, T2 alpha)
             end
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
         | LCF (CSTEP i) $ [] =>
             R.CStep sign i
         | LCF CSYM $ [] =>
             R.CSym
         | LCF CEVAL $ [] =>
             R.CEval sign
         | LCF (REWRITE_GOAL tau) $ [_ \ m] =>
             R.RewriteGoal m
         | LCF EVAL_GOAL $ [] =>
             R.EvalGoal sign
         | LCF (WITNESS tau) $ [_ \ m] =>
             R.Witness m
         | LCF AUTO $ [] =>
             R.AutoStep sign
         | LCF REC $ [(_, [x]) \ t] =>
             Rec (fn T => elaborate sign (VarCtx.insert rho x T) t)
         | `x => VarCtx.lookup rho x
         | _ => raise Fail ("Expected tactic, got: " ^ DebugShowAbt.toString t ^ " which evaluated to " ^ DebugShowAbt.toString t')
    end

  and elaborateM sign rho T (us, mt) =
    let
      val mt' = evalOpen sign mt handle _ => mt
    in
      case out mt' of
           LCF ALL $ [_ \ t'] =>
             (fn alpha => fn jdg =>
               let
                 val (alpha', modulus) = probe alpha
                 val st = T alpha' jdg
                 val beta = prepend us (bite (!modulus) alpha)
               in
                 MT.ALL (elaborate sign rho t' beta) st
               end)
         | LCF EACH $ [_ \ v] =>
             let
               val Ts = List.map (elaborate sign rho) (elaborateVec (evalOpen sign v))
             in
               fn alpha => fn jdg =>
                 let
                   val (alpha', modulus) = probe alpha
                   val st = T alpha' jdg
                   val beta = prepend us (bite (!modulus) alpha)
                 in
                   MT.EACH (List.map (fn T => T beta) Ts) st
                 end
             end
         | LCF (FOCUS i) $ [_ \ t'] =>
             (fn alpha => fn jdg =>
               let
                 val (alpha', modulus) = probe alpha
                 val st = T alpha' jdg
                 val beta = prepend us (bite (!modulus) alpha)
               in
                 MT.FOCUS i (elaborate sign rho t' beta) st
               end)
         | _ => raise Fail ("Expecting multitac but got " ^ DebugShowAbt.toString mt')
    end

  fun elaborate' sign =
    elaborate sign VarCtx.empty
end

structure LcfElaborator = LcfElaborator (Refiner)
