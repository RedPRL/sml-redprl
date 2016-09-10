structure Lcf = DependentLcf (RedPrlJudgment)
structure Tacticals = Tacticals (Lcf)
structure Multitacticals = Multitacticals (Lcf)

functor RefinerKit (Sig : MINI_SIGNATURE) =
struct
  structure E = RedPrlError and O = RedPrlOpData and T = Lcf.T and Abt = RedPrlAbt and Syn = Syntax and Seq = RedPrlSequent and J = RedPrlJudgment
  structure Machine = AbtMachineUtil (RedPrlMachine (Sig))
  local structure TeleNotation = TelescopeNotation (T) in open TeleNotation end
  open RedPrlSequent

  structure CJ = RedPrlCategoricalJudgment

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
        Metavar.named @@ "??" ^ str ^ Int.toString i
      end
  end

  fun makeGoal jdg =
    let
      open Abt infix 1 $#
      val x = newMeta ""
      val vl as (_, tau) = J.evidenceValence jdg
      fun hole ps ms = check (x $# (ps, ms), tau)
    in
      ((x, jdg), hole)
    end


end


