structure LcfLanguage = LcfAbtLanguage (RedPrlAbt)

signature LCF_GENERIC_UTIL = 
sig
  structure Abt : ABT
  datatype 'a generic = || of ((Abt.symbol * Abt.psort) list * (Abt.variable * Abt.sort) list) * 'a
  include LCF_UTIL where type 'a Eff.t = 'a generic

  val genericToAbt : jdg generic -> Abt.abt
  val genericFromAbt : (int -> Abt.symbol) option -> Abt.abt -> jdg generic
end

structure Lcf :
sig
  include LCF_GENERIC_UTIL
  val prettyState : jdg state -> PP.doc
  val stateToString : jdg state -> string
end =
struct
  structure LcfGeneric = LcfGeneric (LcfLanguage)
  structure Def = LcfGenericUtil (structure Lcf = LcfGeneric and J = RedPrlJudgment)
  open Def LcfGeneric
  infix |> ||

  local
    open Abt RedPrlSequent RedPrlOpData
    infix $$ \ >> $
  in
    fun genericToAbt ((syms, vars) || (seq as (H >> jdg))) =
      let
        val (us, sigmas) = ListPair.unzip syms
        val (xs, taus) = ListPair.unzip vars
        val hyps = Hyps.foldr (fn (x, _, r) => x :: r) [] H
        val (_, addrs) = ListPair.foldr (fn (x, x', (i, r)) => (i + 1, if Sym.eq (x, x') then r @ [i] else r)) (0, []) (xs, hyps)
      in
        MONO (GJDG_FORM (sigmas, addrs)) $$ [(us,[]) \ RedPrlSequent.toAbt seq]
      end

    fun genericFromAbt names (gentm : abt) = 
      let
        val MONO (GJDG_FORM (sigmas, addrs)) $ [(us, _) \ seq] = Abt.out gentm
        val H >> concl = RedPrlSequent.fromAbtUsingNames names seq
        val (_, hyps) = Hyps.foldr (fn (x, jdg, (i, r)) => (i + 1, (i, x, jdg) :: r)) (0, []) H
        val hyps' = List.filter (fn (i, x, jdg) => List.exists (fn j => i = j) addrs) hyps
        val hyps'' = List.map (fn (i, x, jdg) => (x, CJ.synthesis jdg)) hyps'
      in
        (ListPair.zip (us, sigmas), hyps'') || (H >> concl)
      end
  end

  val prettySyms =
    PP.text o ListSpine.pretty (fn (u, sigma) => Sym.toString u ^ " : " ^ Abt.O.Ar.Vl.PS.toString sigma) ", "

  val prettyVars = 
    PP.text o ListSpine.pretty (fn (x, tau) => Var.toString x ^ " : " ^ Abt.O.Ar.Vl.S.toString tau) ", "

  fun prettyGoal (syms, vars) (x, jdg) =
    let
      val parametric = 
        if List.length syms > 0 then
          PP.concat [PP.line, PP.text "nabla {", prettySyms syms, PP.text "}. "]
        else
          PP.empty
    in
      PP.concat
        [PP.text "Goal ",
         PP.text (RedPrlAbt.Metavar.toString x),
         PP.text ".",
         parametric,
         PP.nest 2 (PP.concat [PP.line, RedPrlSequent.pretty TermPrinter.toString jdg]),
         PP.line]
    end


  val prettyGoals : jdg eff Tl.telescope -> {doc : PP.doc, env : J.env, idx : int} =
    let
      open RedPrlAbt
    in
      Tl.foldl
        (fn (x, (syms, vars) || jdg, {doc, env, idx}) =>
          let
            val x' = Metavar.named (Int.toString idx)
            val jdg' = J.subst env jdg
            val ((ssorts, vsorts), tau) = J.sort jdg'
            val vl' = ((ssorts @ List.map #2 syms, vsorts @ List.map #2 vars), tau)
            val env' = Metavar.Ctx.insert env x (LcfLanguage.var x' vl')

          in
            {doc = PP.concat [doc, prettyGoal (syms, vars) (x', jdg'), PP.line],
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


