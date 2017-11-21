functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure Tactical = RedPrlTactical (Lcf)

  open Tactical
  infix orelse_ then_

  structure E = RedPrlError and O = RedPrlOpData and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = Syntax and J = RedPrlJudgment
  structure K = RedPrlKind
  structure L = RedPrlLevel
  structure AJ = RedPrlAtomicJudgment
  structure Seq = struct open RedPrlSequentData RedPrlSequent end
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = RedPrlMachine (Sig)

  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent
  infix 2 >: >>

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

  fun makeNamePopper alpha = 
    let
      val ix = ref 0
    in
      fn () => 
        let
          val i = !ix
          val h = alpha i
        in
          ix := i + 1;
          h
        end
    end

  (* assert that the term 'm' has only free variables 'us' and free variables 'xs' at most. *)
  fun assertWellScoped xs m = 
    let
      val vars = List.foldl (fn (x, vars) => Var.Ctx.remove vars x) (Abt.varctx m) xs
      fun ppVars us = Fpp.Atomic.squares @@ Fpp.hsep @@ List.map TermPrinter.ppVar us
      val varsOk = Var.Ctx.isEmpty vars
    in
      if varsOk then
        ()
      else
        raise E.error
          [Fpp.text "Internal Error:",
           Fpp.text "Validation term",
           TermPrinter.ppTerm m,
           Fpp.text "had unbound variables",
           ppVars (Var.Ctx.domain vars),
           Fpp.text "whereas we expected only",
           ppVars xs]
    end

  (* hypotheses *)

  structure Hyps = (* favonia: not sure about the organization *)
  struct
    structure HypsUtil = TelescopeUtil (Seq.Hyps)
    open HypsUtil

    fun toList H =
      Seq.Hyps.foldr (fn (x, jdg, r) => Abt.check (Abt.`x, AJ.synthesis jdg) :: r) [] H

    fun lookup H z =
      Seq.Hyps.lookup H z
      handle _ =>
        raise E.error [Fpp.text "Found nothing in context for hypothesis", TermPrinter.ppVar z]

    (* The telescope lib should be redesigned to make the following helper functions easier.
     * At least the calling convention can be more consistent. *)

    fun substAfter (z, term) H = (* favonia: or maybe (term, z)? I do not know. *)
      Seq.Hyps.modifyAfter z (AJ.map (Abt.substVar (term, z))) H

    fun interposeAfter (z, H') H =
      Seq.Hyps.interposeAfter H z H'

    fun interposeThenSubstAfter (z, H', term) H =
      Seq.Hyps.interposeAfter (Seq.Hyps.modifyAfter z (AJ.map (Abt.substVar (term, z))) H) z H'
  end

  fun @> (H, (x, j)) = Hyps.snoc H x j
  infix @>
  fun |@> h = Hyps.empty @> h

  (* evidence *)

  fun abstractEvidence H m =
    let
      val (xs, taus) = Hyps.foldr (fn (x, jdg, (xs, taus)) => (x::xs, AJ.synthesis jdg::taus)) ([],[]) H
    in
      assertWellScoped xs m;
      Abt.checkb (Abt.\ (xs, m), (taus, Abt.sort m))
    end

  fun #> (psi, (H, m)) =
    Lcf.|> (psi, abstractEvidence H m)
  infix #>

  val trivial = Syn.into Syn.TV

  (* telescope combinators *)

  fun |>: g = T.empty >: g

  fun >:+ (tel, list) : 'a telescope =
    List.foldl (fn (g, t) => t >: g) tel list
  infix 5 >:+

  fun |>:+ g = T.empty >:+ g

  fun >:? (tel, NONE) = tel
    | >:? (tel, SOME g) = tel >: g
  infix 5 >:?

  fun |>:? g = T.empty >:? g

  (* making goals *)

  fun makeGoal jdg =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val (_, tau) = J.sort jdg
      val ms =
        case jdg of
           H >> _ => Hyps.toList H
         | MATCH _ => []
         | MATCH_RECORD _ => []

      val hole = check (x $# ms, tau)
    in
      ((x, jdg), hole)
    end
  fun makeGoal' jdg = #1 @@ makeGoal jdg

  (* needing the realizer *)
  fun makeTrueWith f H (ty, l) = makeGoal @@ Seq.map f @@ H >> AJ.TRUE (ty, l)
  val makeTrue = makeTrueWith (fn j => j)
  fun makeSynth H (m, l) = makeGoal @@ H >> AJ.SYNTH (m, l)
  fun makeMatch part = makeGoal @@ MATCH part
  fun makeMatchRecord part = makeGoal @@ MATCH_RECORD part
  fun makeTerm H tau = makeGoal @@ H >> AJ.TERM tau

  (* ignoring the trivial realizer *)
  fun makeEqWith f H ((m, n), (ty, l)) = makeGoal' @@ Seq.map f @@ H >> AJ.EQ ((m, n), (ty, l))
  val makeEq = makeEqWith (fn j => j)
  fun makeMem H (m, (ty, l)) = makeGoal' @@ H >> AJ.MEM (m, (ty, l))
  fun makeSubType H ((a, b), l, k) = makeGoal' @@ H >> AJ.SUB_TYPE ((a, b), l, k)

  (* conditional goal making *)

  fun makeEqIfDifferent H ((m, n), (ty, l)) =
    if Abt.eq (m, n) then NONE
    else SOME @@ makeEq H ((m, n), (ty, l))

  fun makeEqIfAllDifferent H ((m, n), (ty, l)) ns =
    if List.exists (fn n' => Abt.eq (m, n')) ns then NONE
    else makeEqIfDifferent H ((m, n), (ty, l))

  fun makeSubTypeIfDifferent H ((a, b), l, k) =
    if Abt.eq (a, b) then NONE
    else SOME @@ makeSubType H ((a, b), l, k)

  fun ifAllNone l goal =
    if List.exists Option.isSome l then NONE else SOME goal

  (* internalized EQ_TYPE *)

  structure Universe =
  struct
    val inherentLevel = L.succ
  end
  structure Assert =
  struct
    fun levelMem (l1, l2) =
      if L.< (l1, l2) then
        ()
      else
        E.raiseError @@ E.GENERIC [Fpp.text "Expected level", L.pretty l1, Fpp.text "to be less than", L.pretty l2]
  end
  fun makeEqTypeWith f H ((a, b), l, k) =
    makeEqWith f H ((a, b), (Syn.intoU (l, k), Universe.inherentLevel l))
  val makeEqType = makeEqTypeWith (fn j => j)
  fun makeType H (a, l, k) = makeEqType H ((a, a), l, k)
  fun makeEqTypeIfDifferent H ((a, b), l, k) =
    makeEqIfDifferent H ((a, b), (Syn.intoU (l, k), Universe.inherentLevel l))

  (* aux functions for subtyping *)

  fun isInUsefulUniv (l', k') (l, k) =
    not (OptionUtil.eq L.WK.eq (L.WK.residual ((l, k), (l', k')), SOME (l, k)))

  (* assertions *)

  structure Assert =
  struct
    open Assert
    fun sortEq (tau1, tau2) = 
      if tau1 = tau2 then 
        ()
      else
        raise E.error [Fpp.text "Expected sort", TermPrinter.ppSort tau1, Fpp.text "to be equal to", TermPrinter.ppSort tau2]

    fun alphaEq' msg (m, n) =
      if Abt.eq (m, n) then
        ()
      else
        raise E.error [Fpp.text msg, Fpp.text ":", Fpp.text "Expected", TermPrinter.ppTerm m, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

    fun alphaEq (m, n) =
      if Abt.eq (m, n) then
        ()
      else
        raise E.error [Fpp.text "Expected", TermPrinter.ppTerm m, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

    fun alphaEqEither ((m0, m1), n) =
      if Abt.eq (m0, n) orelse Abt.eq (m1, n) then
        ()
      else
        raise E.error [Fpp.text "Expected", TermPrinter.ppTerm m0, Fpp.text "or", TermPrinter.ppTerm m1, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

    fun levelLeq (l1, l2) =
      if L.<= (l1, l2) then
        ()
      else
        raise E.error [Fpp.text "Expected level", L.pretty l1, Fpp.text "to be less than or equal to", L.pretty l2]

    fun levelEq (l1, l2) =
      if L.eq (l1, l2) then
        ()
      else
        raise E.error [Fpp.text "Expected level", L.pretty l1, Fpp.text "to be equal to", L.pretty l2]

    fun kindLeq (k1, k2) =
      if K.<= (k1, k2) then
        ()
      else
        raise E.error [Fpp.text "Expected kind", TermPrinter.ppKind k1, Fpp.text "to be stronger than or equal to", TermPrinter.ppKind k2]

    fun kindEq (k1, k2) =
      if k1 = k2 then
        ()
      else
        raise E.error [Fpp.text "Expected kind", TermPrinter.ppKind k1, Fpp.text "to be equal to", TermPrinter.ppKind k2]

    fun inUsefulUniv (l', k') (l, k) =
      if isInUsefulUniv (l', k') (l, k) then
        ()
      else
        E.raiseError @@ E.GENERIC [Fpp.text "Expected level", L.pretty l', Fpp.text "and kind", TermPrinter.ppKind k, Fpp.text "to be useful"]

    fun dirEq msg ((r1, r1'), (r2, r2')) =
      if Abt.eq (r1, r2) andalso Abt.eq (r1', r2') then
        ()
      else
        raise E.error
          [Fpp.text (msg ^ ":"),
           Fpp.text "Expected direction",
           TermPrinter.ppTerm r1,
           Fpp.text "~>",
           TermPrinter.ppTerm r1',
           Fpp.text "to be equal to",
           TermPrinter.ppTerm r2,
           Fpp.text "~>",
           TermPrinter.ppTerm r2']

    fun equationEq msg ((r1, r1'), (r2, r2')) =
      if Abt.eq (r1, r2) andalso Abt.eq (r1', r2') then
        ()
      else
        raise E.error
          [Fpp.text (msg ^ ":"),
           Fpp.text "Expected equation",
           TermPrinter.ppTerm r1,
           Fpp.text "=",
           TermPrinter.ppTerm r1',
           Fpp.text "to be equal to",
           TermPrinter.ppTerm r2,
           Fpp.text "=",
           TermPrinter.ppTerm r2']

    fun equationsEq msg = ListPair.mapEq (equationEq msg)

    (* The following is a sufficient condition for tautology:
     * the list contains a true equation `r = r` or both `r = 0`
     * and `r = 1` for some r.
     *)
    structure SymSet = SplaySet (structure Elem = Sym.Ord)
    fun tautologicalEquations msg eqs =
      let
        fun goEqs _ [] = false
          | goEqs (state as (zeros, ones)) ((r1, r2) :: eqs) =
              case (Syn.out r1, Syn.out r2) of
                (Syn.DIM0, Syn.DIM0) => true
              | (Syn.DIM0, Syn.DIM1) => goEqs state eqs
              | (Syn.DIM0, Syn.VAR _) => goEqs state eqs
              | (Syn.DIM0, Syn.META _) => goEqs state eqs
              | (Syn.DIM1, Syn.DIM1) => true
              | (Syn.DIM1, Syn.DIM0) => goEqs state eqs
              | (Syn.DIM1, Syn.VAR _) => goEqs state eqs
              | (Syn.DIM1, Syn.META _) => goEqs state eqs
              | (Syn.VAR (u, _), Syn.DIM0) =>
                  SymSet.member ones u orelse goEqs (SymSet.insert zeros u, ones) eqs
              | (Syn.META (u, _), Syn.DIM0) =>
                  SymSet.member ones u orelse goEqs (SymSet.insert zeros u, ones) eqs
              | (Syn.VAR (u, _), Syn.DIM1) =>
                  SymSet.member zeros u orelse goEqs (zeros, SymSet.insert ones u) eqs
              | (Syn.META (u, _), Syn.DIM1) =>
                  SymSet.member zeros u orelse goEqs (zeros, SymSet.insert ones u) eqs
              | (Syn.VAR (u, _), Syn.VAR (v, _)) => Sym.eq (u, v) orelse goEqs state eqs
              | (Syn.META (u, _), Syn.META (v, _)) => Sym.eq (u, v) orelse goEqs state eqs
              | _ => raise E.error [Fpp.text "Expected equation but got ", TermPrinter.ppTerm r1, Fpp.text "=", TermPrinter.ppTerm r2]
        fun prettyEq (r1, r2) = [TermPrinter.ppTerm r1, Fpp.text "=", TermPrinter.ppTerm r2, Fpp.text ";"]
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
