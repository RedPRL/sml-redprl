functor LcfElaborator (R : REFINER where type symbol = Symbol.t and type abt = Abt.abt) : LCF_ELABORATOR =
struct
  structure Refiner = R
  structure Signature = AbtSignature
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
      handle _ => t


  fun Rec f alpha jdg =
    f (Rec f) alpha jdg

  fun elaborate sign rho t =
    case out (evalOpen sign t) of
         LCF ID $ _ => (fn _ => T.ID)
       | LCF (SEQ _) $ [_ \ t, (us, _) \ mt] =>
           elaborateMulti sign rho (elaborate sign rho t) us mt
       | LCF REC $ [(_, [x]) \ t] =>
           Rec (fn T => elaborate sign (VarCtx.insert rho x T) t)
       | LCF (ELIM {target}) $ [_ \ m] =>
           R.Elim target (elaborateOpt (evalOpen sign m))
       | LCF (INTRO {rule}) $ [_ \ m] =>
           R.Intro rule (elaborateOpt (evalOpen sign m))
       | `x => VarCtx.lookup rho x
       | _ => raise Fail "Expected tactic"

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
