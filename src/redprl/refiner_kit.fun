functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure E = RedPrlError and O = RedPrlOpData and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = Syntax and Seq = RedPrlSequent and J = RedPrlJudgment
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent
  infix >: >>

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

  fun orelse_ (t1, t2) alpha = Lcf.orelse_ (t1 alpha, t2 alpha)
  infix orelse_

  fun >:+ (tel, (l : (label * 'a) list)) : 'a telescope =
    List.foldl (fn (g, t) => t >: g) tel l
  infix 5 >:+

  (* this is a hack till we have a nice way to pre-compose Equality.Symmetry *)
  fun catJdgFlip (CJ.EQ_TYPE (a, b)) = CJ.EQ_TYPE (b, a)
    | catJdgFlip (CJ.EQ ((a, b), ty)) = CJ.EQ ((b, a), ty)
  fun catJdgFlipWrapper tactic alpha (IH >> jdg) =
    tactic alpha (IH >> catJdgFlip jdg)

  fun hypsToSpine H =
    Hyps.foldr (fn (x, jdg, r) => Abt.check (Abt.`x, CJ.synthesis jdg) :: r) [] H

  fun makeGoal jdg =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val vl as (_, tau) = J.sort jdg
      val (ps, ms) =
        case jdg of
           (I, H) >> _ => (List.map (fn (u, sigma) => (P.VAR u, sigma)) I, hypsToSpine H)
         | MATCH _ => ([],[])

      val hole = check (x $# (ps, ms), tau)
    in
      ((x, jdg), hole)
    end


  fun lookupHyp H z =
    Hyps.lookup H z
    handle _ =>
      raise E.error [E.% @@ "Found nothing in context for hypothesis `" ^ Sym.toString z ^ "`"]

  fun assertAlphaEq (m, n) =
    if Abt.eq (m, n) then
      ()
    else
      raise E.error [E.% "Expected", E.! m, E.% "to be alpha-equivalent to", E.! n]

  fun assertParamEq msg (r1, r2) =
    if P.eq Sym.eq (r1, r2) then
      ()
    else
      raise E.error [E.% (msg ^ ":"), E.% "Expected parameter", E.% (P.toString Sym.toString r1), E.% "to be equal to", E.% (P.toString Sym.toString r2)]

  fun assertEquationEq msg ((r1, r1'), (r2, r2')) =
    if P.eq Sym.eq (r1, r2) andalso P.eq Sym.eq (r1', r2') then
      ()
    else
      raise E.error [E.% (msg ^ ":"), E.% "Expected equation", E.% (P.toString Sym.toString r1), E.% "=", E.% (P.toString Sym.toString r1'), E.% "to be equal to", E.% (P.toString Sym.toString r2), E.% "=", E.% (P.toString Sym.toString r2')]

  (* The following is a sufficient condition for tautology:
   * the list contains a true equation `r = r` or both `r = 0`
   * and `r = 1` for some r.
   *)
  structure SymSet = SplaySet (structure Elem = Sym.Ord)
  fun assertTautologicalEquations msg eqs =
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
      fun prettyEq (r1, r2) =
            [E.% (P.toString Sym.toString r1), E.% "=", E.% (P.toString Sym.toString r2), E.% ";"]
    in
      if goEqs (SymSet.empty, SymSet.empty) eqs then
        ()
      else
        (* todo: pretty printer for equation lists *)
        raise E.error
          (List.concat
            [ [E.% (msg ^ ":"), E.% "Expected shape"]
            , ListMonad.bind prettyEq eqs
            , [E.% "to have true equation r = r or equation pair r = 0 and r = 1."]
            ])
    end

  fun assertVarEq (x, y) =
    if Var.eq (x, y) then
      ()
    else
      raise E.error [E.% @@ "Expected variable `" ^ Var.toString x ^ "` to be equal to variable `" ^ Var.toString y ^ "`"]

end


