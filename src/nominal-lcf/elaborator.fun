functor LcfElaborator (R : REFINER) : LCF_ELABORATOR =
struct
  structure Refiner = R
  structure T = R.Tacticals

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

  fun Trace m jdg =
    let
      val x = Abt.Metavariable.named "?"
      val psi = R.Telescope.snoc R.Telescope.empty (x, jdg)
    in
      print (DebugShowAbt.toString m ^ "\n");
      (psi, fn rho => R.Telescope.lookup rho x)
    end

  fun elaborate sign rho t =
    let
      val t' = evalOpen sign t handle _ => t
    in
      case out t' of
           LCF ID $ _ => (fn _ => T.ID)
         | LCF FAIL $ _ => (fn _ => fn _ => raise Fail "Fail")
         | LCF (TRACE _) $ [_ \ m] => (fn _ => Trace m)
         | LCF (SEQ _) $ [_ \ t, (us, _) \ mt] =>
             elaborateMulti sign rho (elaborate sign rho t) us mt
         | LCF REC $ [(_, [x]) \ t] =>
             Rec (fn T => elaborate sign (VarCtx.insert rho x T) t)
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
         | `x => VarCtx.lookup rho x
         | _ => raise Fail ("Expected tactic, got: " ^ DebugShowAbt.toString t ^ " which evaluated to " ^ DebugShowAbt.toString t')
    end

  (* Below, as an optimization, we lazily execute the first tactic whilst
   * calculating its modulus of continuity, rather than executing it twice
   * as in the Definition. *)
  and elaborateMulti sign rho T1 us mt =
    case out (evalOpen sign mt) of
         LCF ALL $ [_ \ t2] =>
           let
             val T2 = elaborate sign rho t2
           in
             fn alpha =>
               let
                 val beta = prepend us alpha
               in
                 fn jdg =>
                   let
                     val (beta', modulus) = probe beta
                     val st = T1 beta' jdg
                   in
                     T.THEN (fn _ => st, T2 (bite (!modulus) beta)) jdg
                   end
               end
           end
       | LCF EACH $ [_ \ v] =>
           let
             val Ts = List.map (elaborate sign rho) (elaborateVec (evalOpen sign v))
           in
             fn alpha =>
               let
                 val beta = prepend us alpha
               in
                 fn jdg =>
                   let
                     val (beta', modulus) = probe beta
                     val st = T1 beta' jdg
                   in
                     T.THENL (fn _ => st, List.map (fn Ti => Ti (bite (!modulus) beta)) Ts) jdg
                   end
               end
           end
       | LCF (FOCUS i) $ [_\ t2] =>
           let
             val T2 = elaborate sign rho t2
           in
             fn alpha =>
               let
                 val beta = prepend us alpha
               in
                 fn jdg =>
                   let
                     val (beta', modulus) = probe beta
                     val st = T1 beta' jdg
                   in
                     T.THENF (fn _ => st, i, T2 (bite (!modulus) beta)) jdg
                   end
               end
           end
       | _ => raise Fail "Expected multitactic"

  fun elaborate' sign =
    elaborate sign VarCtx.empty
end

structure LcfElaborator = LcfElaborator (Refiner)
