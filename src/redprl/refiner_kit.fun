functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure E = RedPrlError and O = RedPrlOpData and T = TelescopeUtil (Lcf.Tl) and Abt = RedPrlAbt and Syn = Syntax and Seq = RedPrlSequent and J = RedPrlJudgment
  structure Env = RedPrlAbt.Metavar.Ctx
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent

  fun @> (H, (x, j)) = Hyps.snoc H x j
  infix @>

  structure P = struct open RedPrlParameterTerm RedPrlParamData end
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

  fun assertVarEq (x, y) =
    if Var.eq (x, y) then
      ()
    else
      raise E.error [E.% @@ "Expected variable `" ^ Var.toString x ^ "` to be equal to variable `" ^ Var.toString y ^ "`"]

end


