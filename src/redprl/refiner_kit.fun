functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure E = RedPrlError and O = RedPrlOpData and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = Syntax and Seq = RedPrlSequent and J = RedPrlJudgment
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent
  infix >:

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


  fun appendListOfGoals (tel, (l : (label * 'a) list)) : 'a telescope =
    List.foldl (fn (g, l) => l >: g) tel l

  fun makeGoal (Lcf.|| (bs, jdg)) =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val vl as (_, tau) = J.sort jdg
      fun hole ps ms = check (x $# (ps, ms), tau) handle _ => raise Fail "makeGoal"
    in
      ((x, Lcf.|| (bs, jdg)), hole)
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

  fun equationEq (r1, r1') (r2, r2') = P.eq Sym.eq (r1, r2) andalso P.eq Sym.eq (r1', r2')

  fun assertEquationEq msg ((r1, r1'), (r2, r2')) =
    if equationEq (r1, r1') (r2, r2') then
      ()
    else
      raise E.error [E.% (msg ^ ":"), E.% "Expected equation", E.% (P.toString Sym.toString r1), E.% "=", E.% (P.toString Sym.toString r1'), E.% "to be equal to", E.% (P.toString Sym.toString r2), E.% "=", E.% (P.toString Sym.toString r2')]

  (* The following is a sufficient condition for tautology:
   * the list contains a true equation `r = r` or both `r = 0`
   * and `r = 1` for some r.
   *)
  fun assertTautologicalEquations msg l =
    if List.exists (P.eq Sym.eq) l then
      ()
    else
      let
        (* O(n^2)-time checking *)
        fun goEquations [] = false
          | goEquations (eq :: eqs) =
              let
                val res = case #2 eq of
                    P.APP d => List.exists (fn e => equationEq (#1 eq, P.APP (RedPrlParamData.invert d)) e) eqs
                  | _ => false
              in
                res orelse goEquations eqs
              end
      in
        if goEquations l then
          ()
        else
          (* todo: pretty printer for equation lists *)
          raise E.error
            (List.concat
              [ [E.% (msg ^ ":"), E.% "Expected shape"]
              , ListMonad.bind (fn (r1, r2) =>
                [E.% (P.toString Sym.toString r1), E.% "=", E.% (P.toString Sym.toString r2), E.% ";"]) l
              , [E.% "to have true equation r = r or equation pair r = 0 and r = 1."]
              ])
      end

  fun assertVarEq (x, y) =
    if Var.eq (x, y) then
      ()
    else
      raise E.error [E.% @@ "Expected variable `" ^ Var.toString x ^ "` to be equal to variable `" ^ Var.toString y ^ "`"]

end


