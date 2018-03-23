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

  (* assert that the term 'm' has only free variables 'xs' at most. *)
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

    fun makeAsEqIfDifferent tr H =
      fn ((a, b), INTERNAL_TYPE ty) => makeEqIfDifferent tr H ((a, b), ty)
       | ((a, b), UNIV_OMEGA k) => makeEqTypeIfDifferent tr H ((a, b), k)

    fun makeAsMem tr H params = makeGoal' tr @@ H >> AJ.View.makeAsMem params

    fun makeAsSubType tr H params = makeGoal' tr @@ H >> AJ.View.makeAsSubType params

    fun makeAsSubTypeIfDifferent tr H =
      fn (a, INTERNAL_TYPE b) => makeSubTypeIfDifferent tr H (a, b)
       | (a, UNIV_OMEGA k) => SOME @@ makeSubKind tr H (a, k)
  end
end
