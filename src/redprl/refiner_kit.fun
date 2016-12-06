structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

structure Lcf :
sig
  include LCF_UTIL
  val prettyState : jdg state -> PP.doc
  val stateToString : jdg state -> string
end =
struct
  structure Def = LcfUtil (structure Lcf = Lcf (LcfLanguage) and J = RedPrlJudgment)
  open Def
  infix |>

  fun prettyGoal (x, jdg) =
    PP.concat
      [PP.text "Goal ",
       PP.text (RedPrlAbt.Metavar.toString x),
       PP.text ".",
       PP.nest 2 (PP.concat [PP.line, RedPrlSequent.pretty TermPrinter.toString jdg]),
       PP.line]

  val prettyGoals : jdg Tl.telescope -> {doc : PP.doc, env : J.env, idx : int} =
    let
      open RedPrlAbt
    in
      Tl.foldl
        (fn (x, jdg, {doc, env, idx}) =>
          let
            val x' = Metavar.named (Int.toString idx)
            val jdg' = J.subst env jdg
            val env' = Metavar.Ctx.insert env x (LcfLanguage.var x' (J.sort jdg'))
          in
            {doc = PP.concat [doc, prettyGoal (x', jdg'), PP.line],
             env = env',
             idx = idx + 1}
          end)
        {doc = PP.empty, env = Metavar.Ctx.empty, idx = 0}
    end

  fun prettyValidation env vld =
    let
      open RedPrlAbt infix \
      val _ \ m = outb vld
    in
      PP.text (TermPrinter.toString (substMetaenv env m))
    end

  fun prettyState (psi |> vld) =
    let
      val {doc = goals, env, idx} = prettyGoals psi
    in
      PP.concat
        [goals,
         PP.newline,
         PP.rule #"-",
         PP.newline,
         PP.text "Current Proof Extract:",
         PP.newline,
         PP.rule #"-",
         PP.newline, PP.newline,
         prettyValidation env vld]
    end

  val stateToString : jdg state -> string =
    PP.toString 80 false o prettyState
end

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

  fun makeGoal jdg =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val vl as (_, tau) = J.sort jdg
      fun hole ps ms = check (x $# (ps, ms), tau)
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

  fun assertVarEq (x, y) =
    if Var.eq (x, y) then
      ()
    else
      raise E.error [E.% @@ "Expected variable `" ^ Var.toString x ^ "` to be equal to variable `" ^ Var.toString y ^ "`"]

end


