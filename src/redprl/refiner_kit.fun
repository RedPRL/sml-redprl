functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure Tactical = RedPrlTactical (Lcf)

  open Tactical
  infix orelse_ then_

  structure E = RedPrlError and O = RedPrlOpData and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = Syntax and Seq = RedPrlSequent and J = RedPrlJudgment
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = RedPrlMachine (Sig)
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent
  infix 2 >: >>

  structure P = struct open RedPrlSortData RedPrlParameterTerm RedPrlParamData end
  structure K = RedPrlKind
  structure CJ = RedPrlCategoricalJudgment

  exception todo
  fun ?e = raise e

  fun @@ (f, x) = f x
  infixr @@

  local
    val counter = ref 0
  in
    fun newMeta str =
      let
        val i = !counter
      in
        counter := i + 1;
        Metavar.named @@ str ^ Int.toString i
      end
  end

  (* assert that the term 'm' has only free symbols 'us' and free variables 'xs' at most. *)
  fun assertWellScoped (us, xs) m = 
    let
      val syms = List.foldl (fn (u, syms) => Sym.Ctx.remove syms u) (Abt.symctx m) us
      val vars = List.foldl (fn (x, vars) => Var.Ctx.remove vars x) (Abt.varctx m) xs
      fun ppSyms us = Fpp.Atomic.braces @@ Fpp.hsep @@ List.map TermPrinter.ppSym us
      fun ppVars us = Fpp.Atomic.squares @@ Fpp.hsep @@ List.map TermPrinter.ppVar us

      val symsOk = Sym.Ctx.foldl (fn (u, sigma, ok) => sigma = O.OPID andalso ok) true syms
      val varsOk = Var.Ctx.isEmpty vars
    in
      if symsOk andalso varsOk then
        ()
      else
        raise E.error
          [Fpp.text "Internal Error:",
           Fpp.text "Validation term",
           TermPrinter.ppTerm m,
           Fpp.text "had unbound symbols",
           ppSyms (Sym.Ctx.domain syms),
           Fpp.text "and unbound variables",
           ppVars (Var.Ctx.domain vars),
           Fpp.text "whereas we expected only",
           ppSyms us,
           Fpp.text "and",
           ppVars xs]
    end


  fun abstractEvidence (I : (sym * psort) list, H) m =
    let
      val (us, sigmas) = ListPair.unzip I
      val (xs, taus) = Hyps.foldr (fn (x, jdg, (xs, taus)) => (x::xs, CJ.synthesis jdg::taus)) ([],[]) H
    in
      assertWellScoped (us, xs) m;
      Abt.checkb (Abt.\ ((us, xs), m), ((sigmas, taus), Abt.sort m))
    end

  fun #> (psi, (I, H, m)) =
    Lcf.|> (psi, abstractEvidence (I, H) m)
  infix #>

  val trivial = Syn.into Syn.TV

  (* telescope combinators *)

  fun |>: g = T.empty >: g

  fun >:+ (tel, list) : 'a telescope =
    List.foldl (fn (g, t) => t >: g) tel list
  infix 5 >:+

  fun |>:+ g = g

  fun >:? (tel, NONE) = tel
    | >:? (tel, SOME g) = tel >: g
  infix 5 >:?

  fun |>:? g = T.empty >:? g

  (* hypotheses *)

  fun @> (H, (x, j)) = Hyps.snoc H x j
  infix @>
  fun |@> h = Hyps.empty @> h

  structure Hyps = (* favonia: not sure about the organization *)
  struct
    structure HypsUtil = TelescopeUtil (Hyps)
    open HypsUtil

    fun toSpine H =
      Hyps.foldr (fn (x, jdg, r) => Abt.check (Abt.`x, CJ.synthesis jdg) :: r) [] H

    fun lookup z H =
      Hyps.lookup H z
      handle _ =>
        raise E.error [Fpp.text "Found nothing in context for hypothesis", TermPrinter.ppSym z]

    (* The telescope lib should be redesigned to make the following helper functions easier.
     * At least the calling convention can be more consistent. *)

    fun substAfter (z, term) H = (* favonia: or maybe (term, z)? I do not know. *)
      Hyps.modifyAfter z (CJ.map_ (Abt.substVar (term, z))) H

    fun interposeAfter (z, H') H =
      Hyps.interposeAfter H z H'

    fun interposeThenSubstAfter (z, H', term) H =
      Hyps.interposeAfter (Hyps.modifyAfter z (CJ.map_ (Abt.substVar (term, z))) H) z H'
  end

  (* making goals *)

  fun makeGoal jdg =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val (_, tau) = J.sort jdg
      val (ps, ms) =
        case jdg of
           (I, H) >> _ => (List.map (fn (u, sigma) => (P.VAR u, sigma)) I, Hyps.toSpine H)
         | MATCH _ => ([],[])
         | MATCH_RECORD _ => ([],[])

      val hole = check (x $# (ps, ms), tau)
    in
      ((x, jdg), hole)
    end
  fun makeGoal' jdg = #1 @@ makeGoal jdg

  (* needing the realizer *)
  fun makeTrue (I, H) (a, k) = makeGoal @@ (I, H) >> CJ.TRUE (a, k)
  fun makeSynth (I, H) (m, k) = makeGoal @@ (I, H) >> CJ.SYNTH (m, k)
  fun makeMatch part = makeGoal @@ MATCH part
  fun makeMatchRecord part = makeGoal @@ MATCH_RECORD part
  fun makeTerm (I, H) tau = makeGoal @@ (I, H) >> CJ.TERM tau
  fun makeDimSubst (I, H) (r, u, m) = makeGoal @@ (I, H) >> CJ.PARAM_SUBST ([(r, O.DIM, u)], m, Abt.sort m)

  (* ignoring the trivial realizer *)
  fun makeType (I, H) (a, k) = makeGoal' @@ (I, H) >> CJ.TYPE (a, k)
  fun makeEqType (I, H) ((a, b), k) = makeGoal' @@ (I, H) >> CJ.EQ_TYPE ((a, b), k)
  fun makeEq (I, H) ((m, n), (ty, k)) = makeGoal' @@ (I, H) >> CJ.EQ ((m, n), (ty, k))
  fun makeMem (I, H) (m, (ty, k)) = makeGoal' @@ (I, H) >> CJ.MEM (m, (ty, k))

  (* conditional goal making *)

  fun makeEqTypeIfDifferent (I, H) ((m, n), k) =
    if Abt.eq (m, n) then NONE
    else SOME @@ makeEqType (I, H) ((m, n), k)

  fun makeEqTypeIfAllDifferentOrLess (I, H) ((m, n), k) ns =
    if List.exists (fn n' => Abt.eq (m, n')) ns
    then SOME @@ makeType (I, H) (m, k)
    else makeEqTypeIfDifferent (I, H) ((m, n), k)

  fun makeTypeIfLess (I, H) (m, k) k' =
    case K.greatestMeetComplement' (k, k') of
      NONE => NONE
    | SOME k'' => SOME @@ makeType (I, H) (m, k'')

  fun makeEqTypeIfDifferentOrLess (I, H) ((m, n), k) k' =
    if Abt.eq (m, n) then makeTypeIfLess (I, H) (m, k) k'
    else SOME @@ makeEqType (I, H) ((m, n), k)

  fun makeEqIfDifferent (I, H) ((m, n), (ty, k)) =
    if Abt.eq (m, n) then NONE
    else SOME @@ makeEq (I, H) ((m, n), (ty, k))

  fun makeEqIfAllDifferent (I, H) ((m, n), (ty, k)) ns =
    if List.exists (fn n' => Abt.eq (m, n')) ns then NONE
    else makeEqIfDifferent (I, H) ((m, n), (ty, k))

  fun makeMemIfLess (I, H) (m, (ty, k)) k' =
    case K.greatestMeetComplement' (k, k') of
      NONE => NONE
    | SOME k'' => SOME @@ makeMem (I, H) (m, (ty, k''))

  fun makeEqIfDifferentOrLess (I, H) ((m, n), (ty, k)) k' =
    if Abt.eq (m, n) then makeMemIfLess (I, H) (m, (ty, k)) k'
    else SOME @@ makeEq (I, H) ((m, n), (ty, k))

  fun makeEqIfAllDifferentOrLess (I, H) ((m, n), (ty, k)) ns k' =
    if List.exists (fn n' => Abt.eq (m, n')) ns
    then makeMemIfLess (I, H) (m, (ty, k)) k'
    else makeEqIfDifferentOrLess (I, H) ((m, n), (ty, k)) k'

  fun ifAllNone l goal =
    if List.exists Option.isSome l then NONE else SOME goal

  (* variable kit *)

  structure VarKit =
  struct
    fun ctxFromList l = List.foldl
          (fn ((tm, x), dict) => Var.Ctx.insert dict x tm)
          Var.Ctx.empty l

    fun toExp x = Syn.into @@ Syn.VAR (x, O.EXP)

    val renameMany = Abt.renameVars o ctxFromList
    fun rename r = renameMany [r]

    val substMany = Abt.substVarenv o ctxFromList
    fun subst s = substMany [s]
  end

  (* assertions *)

  structure Assert =
  struct
    fun sortEq (tau1, tau2) = 
      if tau1 = tau2 then 
        ()
      else
        raise E.error [Fpp.text "Expected sort", TermPrinter.ppSort tau1, Fpp.text "to be equal to", TermPrinter.ppSort tau2]

    fun alphaEq (m, n) =
      if Abt.eq (m, n) then
        ()
      else
        raise E.error [Fpp.text "Expected", TermPrinter.ppTerm m, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

    fun kindLeq (k1, k2) =
      if K.leq (k1, k2) then
        ()
      else
        raise E.error [Fpp.text "Expected kind", TermPrinter.ppKind k1, Fpp.text "to be less than", TermPrinter.ppKind k2]

    fun paramEq msg (r1, r2) =
      if P.eq Sym.eq (r1, r2) then
        ()
      else
        raise E.error [Fpp.text (msg ^ ":"), Fpp.text "Expected parameter", TermPrinter.ppParam r1, Fpp.text "to be equal to", TermPrinter.ppParam r2]

    fun equationEq msg ((r1, r1'), (r2, r2')) =
      if P.eq Sym.eq (r1, r2) andalso P.eq Sym.eq (r1', r2') then
        ()
      else
        raise E.error
          [Fpp.text (msg ^ ":"),
           Fpp.text "Expected equation",
           TermPrinter.ppParam r1,
           Fpp.text "=",
           TermPrinter.ppParam r1',
           Fpp.text "to be equal to",
           TermPrinter.ppParam r2,
           Fpp.text "=",
           TermPrinter.ppParam r2']

    (* The following is a sufficient condition for tautology:
     * the list contains a true equation `r = r` or both `r = 0`
     * and `r = 1` for some r.
     *)
    structure SymSet = SplaySet (structure Elem = Sym.Ord)
    fun tautologicalEquations msg eqs =
      let
        fun goEqs _ [] = false
          | goEqs (state as (zeros, ones)) (eq :: eqs) =
              case eq of
                (P.APP P.DIM0, P.APP P.DIM0) => true
              | (P.APP P.DIM0, _) => goEqs state eqs
              | (P.APP P.DIM1, P.APP P.DIM1) => true
              | (P.APP P.DIM1, _) => goEqs state eqs
              | (P.VAR u, P.APP P.DIM0) =>
                  SymSet.member ones u orelse goEqs (SymSet.insert zeros u, ones) eqs
              | (P.VAR u, P.APP P.DIM1) =>
                  SymSet.member zeros u orelse goEqs (zeros, SymSet.insert ones u) eqs
              | (P.VAR u, P.VAR v) => Sym.eq (u, v) orelse goEqs state eqs
        fun prettyEq (r1, r2) = [TermPrinter.ppParam r1, Fpp.text "=", TermPrinter.ppParam r2, Fpp.text ";"]
      in
        if goEqs (SymSet.empty, SymSet.empty) eqs then
          ()
        else
          (* todo: pretty printer for equation lists *)
          raise E.error
            (List.concat
              [ [Fpp.text (msg ^ ":"), Fpp.text "Expected shape"]
              , ListMonad.bind prettyEq eqs
              , [Fpp.text "to have true equation r = r or equation pair r = 0 and r = 1."]
              ])
      end

    fun varEq (x, y) =
      if Var.eq (x, y) then
        ()
      else
        raise E.error [Fpp.text "Expected variable", TermPrinter.ppVar x, Fpp.text "to be equal to variable", TermPrinter.ppVar y]

    fun labelEq msg (lbl0, lbl1) =
      if lbl0 = lbl1 then
        ()
      else
        raise E.error [Fpp.text msg, Fpp.char #":", Fpp.text "Expected label", TermPrinter.ppLabel lbl0, Fpp.text "to be equal to label", TermPrinter.ppLabel lbl1]

    fun labelsEq msg (l0, l1) =
      ListPair.appEq (labelEq msg) (l0, l1)
  end
end
