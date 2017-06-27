functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure Tactical = NominalLcfTactical (structure Lcf = Lcf and Spr = UniversalSpread)
  open Tactical
  infix orelse_ then_

  structure E = RedPrlError and O = RedPrlOpData and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = Syntax and Seq = RedPrlSequent and J = RedPrlJudgment
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent
  infix 2 >: >>

  fun @> (H, (x, j)) = Hyps.snoc H x j
  infix @>

  structure P = struct open RedPrlSortData RedPrlParameterTerm RedPrlParamData end
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

  fun abstractEvidence (I : (sym * psort) list, H) m =
    let
      val (us, sigmas) = ListPair.unzip I
      val (xs, taus) = Hyps.foldr (fn (x, jdg, (xs, taus)) => (x::xs, CJ.synthesis jdg::taus)) ([],[]) H
    in
      Abt.checkb (Abt.\ ((us, xs), m), ((sigmas, taus), Abt.sort m))
    end

  fun #> (psi, (I, H, m)) =
    Lcf.|> (psi, abstractEvidence (I, H) m)
  infix #>

  val trivial = Syn.into Syn.AX

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

  (* hypotheses *)

  fun hypsToSpine H =
    Hyps.foldr (fn (x, jdg, r) => Abt.check (Abt.`x, CJ.synthesis jdg) :: r) [] H

  fun lookupHyp H z =
    Hyps.lookup H z
    handle _ =>
      raise E.error [Fpp.text "Found nothing in context for hypothesis", TermPrinter.ppSym z]

  (* making goals *)

  fun makeGoal jdg =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val (_, tau) = J.sort jdg
      val (ps, ms) =
        case jdg of
           (I, H) >> _ => (List.map (fn (u, sigma) => (P.VAR u, sigma)) I, hypsToSpine H)
         | MATCH _ => ([],[])

      val hole = check (x $# (ps, ms), tau)
    in
      ((x, jdg), hole)
    end
  fun makeGoal' jdg = #1 @@ makeGoal jdg

  (* needing the realizer *)
  fun makeTrue (I, H) a = makeGoal @@ (I, H) >> CJ.TRUE a
  fun makeSynth (I, H) m = makeGoal @@ (I, H) >> CJ.SYNTH m
  fun makeMatch part = makeGoal @@ MATCH part

  (* ignoring the trivial realizer *)
  fun makeType (I, H) a = makeGoal' @@ (I, H) >> CJ.TYPE a
  fun makeEqType (I, H) (a, b) = makeGoal' @@ (I, H) >> CJ.EQ_TYPE (a, b)
  fun makeEq (I, H) ((m, n), ty) = makeGoal' @@ (I, H) >> CJ.EQ ((m, n), ty)
  fun makeMem (I, H) (m, ty) = makeGoal' @@ (I, H) >> CJ.MEM (m, ty)

  (* conditional goal making *)
  fun makeEqTypeIfDifferent (I, H) (m, n) =
    if Abt.eq (m, n) then NONE
    else SOME (makeGoal' @@ (I, H) >> CJ.EQ_TYPE (m, n))

  fun makeEqTypeIfAllDifferent (I, H) (m, n) ns =
    if List.exists (fn n' => Abt.eq (m, n')) ns then NONE
    else makeEqTypeIfDifferent (I, H) (m, n)

  fun makeEqIfDifferent (I, H) ((m, n), ty) =
    if Abt.eq (m, n) then NONE
    else SOME (makeGoal' @@ (I, H) >> CJ.EQ ((m, n), ty))

  fun makeEqIfAllDifferent (I, H) ((m, n), ty) ns =
    if List.exists (fn n' => Abt.eq (m, n')) ns then NONE
    else makeEqIfDifferent (I, H) ((m, n), ty)

  structure Assert =
  struct
    fun alphaEq (m, n) =
      if Abt.eq (m, n) then
        ()
      else
        raise E.error [Fpp.text "Expected", TermPrinter.ppTerm m, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

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
  end
end
