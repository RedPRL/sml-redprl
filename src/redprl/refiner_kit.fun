functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure Tactical = RedPrlTactical (Lcf)

  open Tactical
  infix orelse_ then_

  structure E = RedPrlError and O = RedPrlOperator and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = SyntaxView and J = RedPrlJudgment
  structure K = RedPrlKind
  structure L = RedPrlLevel
  structure AJ = AtomicJudgment
  structure Seq = Sequent
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = RedPrlMachine (Sig)

  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open Sequent
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

  val axiom = Syn.into Syn.AX

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

  fun makeGoal (tr : string list) (jdg : jdg) : (Lcf.L.var * jdg Lcf.I.t) * abt =
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
      ((x, Lcf.::@ (tr, jdg)), hole)
    end

  fun makeGoalWith tr f = makeGoal tr o Seq.map f

  fun makeGoal' tr jdg = #1 @@ makeGoal tr jdg
  fun makeGoal'With tr f = makeGoal' tr o Seq.map f

  (* needing the realizer *)
  fun makeTrueWith tr f H ty = makeGoalWith tr f @@ H >> AJ.TRUE ty
  fun makeTrue tr H ty = makeGoal tr @@ H >> AJ.TRUE ty
  fun makeSynth tr H m = makeGoal tr @@ H >> AJ.SYNTH m
  fun makeMatch tr part = makeGoal tr @@ MATCH part
  fun makeMatchRecord tr part = makeGoal tr @@ MATCH_RECORD part
  fun makeTerm tr H tau = makeGoal tr @@ H >> AJ.TERM tau

  (* ignoring the trivial realizer *)
  fun makeType tr H (a, k) = makeGoal' tr @@ H >> AJ.TYPE (a, k)
  fun makeEqTypeWith tr f H ((a, b), k) = makeGoal'With tr f @@ H >> AJ.EQ_TYPE ((a, b), k)
  fun makeEqType tr H ((a, b), k) = makeGoal' tr @@ H >> AJ.EQ_TYPE ((a, b), k)
  fun makeEqWith tr f H ((m, n), ty) = makeGoal'With tr f @@ H >> AJ.EQ ((m, n), ty)
  fun makeEq tr H ((m, n), ty) = makeGoal' tr @@ H >> AJ.EQ ((m, n), ty)
  fun makeMem tr H (m, ty) = makeGoal' tr @@ H >> AJ.MEM (m, ty)
  fun makeSubType tr H (a, b) = makeGoal' tr @@ H >> AJ.SUB_TYPE (a, b)
  fun makeSubKind tr H (u, k) = makeGoal' tr @@ H >> AJ.SUB_KIND (u, k)

  (* conditional goal making *)

  fun makeEqTypeIfDifferent tr H ((m, n), k) =
    if Abt.eq (m, n) then NONE
    else SOME @@ makeEqType tr H ((m, n), k)

  fun makeEqTypeUnlessSubUniv tr H ((m, n), k) k' =
    Option.map
      (fn k => makeEqType tr H ((m, n), k))
      (K.residual (k, k'))
  
  fun makeTypeUnlessSubUniv tr H (m, k) k' =
    makeEqTypeUnlessSubUniv tr H ((m, m), k) k'

  fun makeEqTypeIfDifferentOrNotSubUniv tr H ((m, n), k) k' =
    if Abt.eq (m, n) then makeTypeUnlessSubUniv tr H (m, k) k'
    else SOME @@ makeEqType tr H ((m, n), k)

  fun makeEqIfDifferent tr H ((m, n), ty) =
    if Abt.eq (m, n) then NONE
    else SOME @@ makeEq tr H ((m, n), ty)

  fun makeEqIfAllDifferent tr H ((m, n), ty) ns =
    if List.exists (fn n' => Abt.eq (m, n')) ns then NONE
    else makeEqIfDifferent tr H ((m, n), ty)

  (* subtyping *)

  fun isInUsefulUnivOmega (k', k) =
    not (OptionUtil.eq K.eq (K.residual (k, k'), SOME k))

  (* It is not clear how exactly the subtyping should be implemented;
   * therefore we have a dummy implementation here. *)
  fun makeSubTypeIfDifferent tr H (a, b) =
    if Abt.eq (a, b) then NONE
    else SOME @@ makeSubType tr H (a, b)

  (* functions which blur the difference between EQ and EQ_TYPE *)
  structure View =
  struct
    datatype as_level = datatype AJ.View.as_level
    datatype as_type = datatype AJ.View.as_type

    val matchTrueAsEq = AJ.View.matchTrueAsEq
    
    fun makeEqAsTrue tr H params = makeGoal' tr @@ H >> AJ.View.makeEqAsTrue params

    val matchAsEqType = AJ.View.matchAsEqType

    fun makeAsEqType tr H params = makeGoal' tr @@ H >> AJ.View.makeAsEqType params

    fun makeAsEqTypeWith tr f H params = makeGoal'With tr f @@ H >> AJ.View.makeAsEqType params

    val matchAsEq = AJ.View.matchAsEq

    fun makeAsEq tr H params = makeGoal' tr @@ H >> AJ.View.makeAsEq params
    fun makeAsEqWith tr f H params = makeGoal'With tr f @@ H >> AJ.View.makeAsEq params

    fun makeAsMem tr H params = makeGoal' tr @@ H >> AJ.View.makeAsMem params

    fun makeAsSubType tr H params = makeGoal' tr @@ H >> AJ.View.makeAsSubType params

    fun makeAsSubTypeIfDifferent tr H =
      fn (a, INTERNAL_TYPE b) => makeSubTypeIfDifferent tr H (a, b)
       | (a, UNIV_OMEGA k) => SOME @@ makeSubKind tr H (a, k)
  end

  (* assertions *)

  structure Assert =
  struct
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

    fun levelLt (l1, l2) =
      if L.< (l1, l2) then
        ()
      else
        raise E.error [Fpp.text "Expected level", TermPrinter.ppTerm (L.into l1), Fpp.text "to be less than", TermPrinter.ppTerm (L.into l2)]

    fun levelLeq (l1, l2) =
      if L.<= (l1, l2) then
        ()
      else
        raise E.error [Fpp.text "Expected level", TermPrinter.ppTerm (L.into l1), Fpp.text "to be less than or equal to", TermPrinter.ppTerm (L.into l2)]

    fun levelEq (l1, l2) =
      if L.eq (l1, l2) then
        ()
      else
        raise E.error [Fpp.text "Expected level", TermPrinter.ppTerm (L.into l1), Fpp.text "to be equal to", TermPrinter.ppTerm (L.into l2)]

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

    fun inUsefulUnivOmega (k', k) =
      if isInUsefulUnivOmega (k', k) then
        ()
      else
        E.raiseError @@ E.GENERIC [Fpp.text "Expected kind", TermPrinter.ppKind k', Fpp.text "to be useful for kind", TermPrinter.ppKind k]

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

  structure View =
  struct
    open View
    structure Assert =
    struct
      val levelLeq =
        fn (_, OMEGA) => ()
         | (l0, FINITE l1) => Assert.levelLeq (l0, l1)
      val levelLt =
        fn (_, OMEGA) => ()
         | (l0, FINITE l1) => Assert.levelLt (l0, l1)
      fun univMem ((l0,k0), (l1,k1)) = (levelLt (l0,l1); Assert.kindLeq (k0,k1))
    end
  end
end
