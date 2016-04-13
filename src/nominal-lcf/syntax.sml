structure NominalLcfSyntax : NOMINAL_LCF_SYNTAX =
struct
  open Abt
  structure O = OperatorData and N = NominalLcfOperatorData and S = SortData

  infix $ \ $#

  type statement = abt
  type multitactic = abt
  type tactic = abt
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
        val psi = metactx m
      in
        case m' of
           O.LCF (N.HYP_VAR a) $ _ =>
             if SymCtx.member syms a then
               m
             else
               check' (`a, S.EXP)
         | theta $ es =>
             check psi (theta $ List.map (goAbs syms) es, tau)
         | x $# (us, ms) =>
             check psi (x $# (us, List.map (go syms) ms), tau)
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

  structure Multi =
  struct
    exception InvalidMultitactic

    datatype view =
        ALL of statement
      | EACH of statement list
      | FOCUS of int * statement

    fun out sign mtac =
      case Abt.out (expandHypVars (evalOpen sign mtac)) of
           O.LCF N.ALL $ [_ \ stmt] => ALL stmt
         | O.LCF N.EACH $ [_ \ vec] => EACH (outVec vec)
         | O.LCF (N.FOCUS i) $ [_ \ stmt] => FOCUS (i, stmt)
         | _ => raise InvalidMultitactic
  end

  structure Stmt =
  struct
    exception InvalidStatement

    type 'a binding = symbol list * 'a

    datatype view =
        SEQ of multitactic binding list
      | TAC of tactic
      | VAR of variable

    fun collect stmt =
      case Abt.out stmt of
           O.LCF (N.SEQ _) $ [_ \ mtac, (us, _) \ stmt] =>
             (us, mtac) :: collect stmt
         | _ => [([], Abt.check (Abt.metactx stmt) (O.LCF N.ALL $ [([],[]) \ stmt], S.MTAC))]

    fun out sign stmt =
      let
        val stmt' = expandHypVars (evalOpen sign stmt)
      in
        case Abt.out stmt' of
             O.LCF (N.SEQ _) $ _ => SEQ (collect stmt')
           | `x => VAR x
           | _ => TAC stmt'
      end
  end
end
