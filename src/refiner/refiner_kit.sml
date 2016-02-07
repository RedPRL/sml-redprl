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
           CTT (EQ EXP) $ [_ \ m, _ \ n, _ \ a] => (m,n,a)
         | _ => raise Fail @@ "Expected equality type, but got " ^ DebugShowAbt.toString m

    fun destUniv m =
      case out m of
           CTT UNIV $ [_ \ i] => i
         | _ => raise Fail @@ "Expected universe, but got " ^ DebugShowAbt.toString m
  end
end
