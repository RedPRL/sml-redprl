structure RefinerKit =
struct
  structure Ctx = SymbolTelescope and Signature = AbtSignature
  structure Lcf = DependentLcf (Judgment)
  structure Telescope = Lcf.T and T = Lcf.T
  structure Tacticals = Tacticals(Lcf)

  type 'a choice_sequence = int -> 'a
  type name_store = Abt.symbol choice_sequence
  type ntactic = name_store -> Tacticals.Lcf.tactic

  local
    val counter = ref 0
  in
    fun newMeta str =
      let
        val i = !counter
      in
        counter := i + 1;
        Metavariable.named ("?" ^ str ^ Int.toString i)
      end
  end


  fun @@ (f,x) = f x
  infix 0 @@

  open Abt Sequent infix $ \ >>

  (* for development *)
  exception hole
  fun ?x = raise x

  local
    exception Destruct
  in
    fun destruct m (theta : unit Operator.t) =
      case out m of
           theta' $ es =>
             if Operator.eq (fn _ => true) (Operator.map (fn _ => ()) theta', theta) then
               (Operator.support theta', es)
             else
               raise Destruct
         | _ => raise Destruct
      handle Destruct =>
        raise Fail @@ "Expected " ^ Operator.toString (fn _ => "-") theta
  end

  fun ^! (m, theta) =
    destruct m theta

  infix ^!

  local
    open OperatorData CttOperatorData SortData
  in
    fun destEq m =
      case out m of
           CTT (EQ tau) $ [_ \ m, _ \ n, _ \ a] => (tau, m,n,a)
         | _ => raise Fail @@ "Expected equality type, but got " ^ DebugShowAbt.toString m

    fun destUniv m =
      case out m of
           CTT (UNIV tau) $ [_ \ i] => (tau, i)
         | _ => raise Fail @@ "Expected universe, but got " ^ DebugShowAbt.toString m

    fun destCEquiv P =
      case (out P) of
           CTT (CEQUIV tau) $ [_ \ m, _ \ n] =>
             let
               val tau1 = sort m
               val tau2 = sort n
               val () =
                 if tau1 = tau2 andalso tau = tau1 then
                   ()
                 else
                   raise Fail "Incompatible sorts in CEquiv"
             in
               (tau, m, n)
             end
         | _ => raise Fail "Expected CEquiv"

    fun makeEq mctx (m,n,a) =
      check
        mctx
        (CTT (EQ (sort m)) $ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a],
         EXP)

    fun makeCEquiv mctx (m,n) =
      check
        mctx
        (CTT (CEQUIV (sort m)) $ [([],[]) \ m, ([],[]) \ n],
         EXP)

    fun makeMember mctx (m,a) =
      check
        mctx
        (CTT (MEMBER (sort m)) $ [([],[]) \ m, ([],[]) \ a],
         EXP)

    fun makeSquash mctx tau a =
      check
        mctx
        (CTT (SQUASH tau) $ [([],[]) \ a],
         EXP)

    fun makeEqSequent H args =
      H >> (makeEq (#metactx H) args, TRIV)

    fun makeMemberSequent H args =
      H >> (makeMember (#metactx H) args, TRIV)

    fun makeLevelSequent (H : Sequent.context) =
      let
        val H' =
          {metactx = #metactx H,
           symctx = #symctx H,
           hypctx = Ctx.empty}
      in
        H' >> (check' (CTT (BASE LVL) $ [], EXP), LVL)
      end


    val makeAx = check' (CTT AX $ [], TRIV)
  end

end
