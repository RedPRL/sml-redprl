structure NominalLcfSyntax : NOMINAL_LCF_SYNTAX =
struct
  open Abt
  structure SymCtx = Symbol.Ctx and VarCtx = Variable.Ctx
  structure O = OperatorData and N = NominalLcfOperatorData and S = SortData

  infix $ \ $#

  type atom = symbol
  type rule = abt
  type tactic = abt
  type multitactic = abt
  type sign = AbtSignature.sign

  exception hole
  fun ?e = raise e

  fun evalOpen sign t =
    DynamicsUtil.evalOpen sign t
      handle _ => t

  local
    fun go syms m =
      let
        val (m', tau) = infer m
      in
        case m' of
           O.LCF (N.HYP_VAR a) $ _ =>
             if SymCtx.member syms a then
               m
             else
               check (`a, S.EXP)
         | theta $ es =>
             check (theta $ List.map (goAbs syms) es, tau)
         | x $# (us, ms) =>
             check (x $# (us, List.map (go syms) ms), tau)
         | _ => m
      end
    and goAbs syms ((us,xs) \ m) =
      let
        val syms' = List.foldl (fn (u, acc) => SymCtx.insert acc u ()) syms us
      in
        (us,xs) \ go syms' m
      end
  in
    (* Replace hypothesis-references @u with variables `u; this will *only* expand
     * unbound hyp-refs. *)
   val expandHypVars =
      go SymCtx.empty
  end

  fun outVec vec =
    case Abt.out vec of
         O.VEC_LIT _ $ es => List.map (fn (_ \ n) => n) es
       | _ => raise Fail "Expected vector argument"

  structure Multitactic =
  struct
    exception InvalidMultitactic

    datatype view =
        ALL of tactic
      | EACH of tactic list
      | FOCUS of int * tactic

    fun out sign mtac =
      case Abt.out (expandHypVars (evalOpen sign mtac)) of
           O.LCF N.ALL $ [_ \ stmt] => ALL stmt
         | O.LCF N.EACH $ [_ \ vec] => EACH (outVec vec)
         | O.LCF (N.FOCUS i) $ [_ \ stmt] => FOCUS (i, stmt)
         | _ => raise InvalidMultitactic
  end

  structure Tactic =
  struct
    exception InvalidStatement

    type 'a binding = symbol list * 'a

    datatype view =
        SEQ of multitactic binding list
      | ORELSE of tactic * tactic
      | REC of variable * tactic
      | PROGRESS of tactic
      | RULE of rule
      | VAR of variable

    fun collect stmt =
      case Abt.out stmt of
           O.LCF (N.SEQ _) $ [_ \ mtac, (us, _) \ stmt] =>
             (us, mtac) :: collect stmt
         | _ => [([], Abt.check (O.LCF N.ALL $ [([],[]) \ stmt], S.MTAC))]

    fun out sign stmt =
      let
        val stmt' = expandHypVars (evalOpen sign stmt)
      in
        case Abt.out stmt' of
             O.LCF (N.SEQ _) $ _ => SEQ (collect stmt')
           | O.LCF N.ORELSE $ [_ \ tac1, _ \ tac2] => ORELSE (tac1, tac2)
           | O.LCF N.REC $ [(_, [x]) \ tac] => REC (x, tac)
           | O.LCF N.PROGRESS $ [_ \ tac] => PROGRESS tac
           | `x => VAR x
           | _ => RULE stmt'
      end
  end
end
