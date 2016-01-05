functor ScriptOperator
  (structure Arity : ARITY where type 'a Valence.Spine.t = 'a list
   val EXP : Arity.Valence.sort
   val TAC : Arity.Valence.sort) :> SCRIPT_OPERATOR =
struct
  open ScriptOperatorData

  structure Arity = Arity
  type 'i t = 'i script_operator

  local
    fun * (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun <> (a, b) = (a, b) (* valence *)
    fun ->> (a, b) = (a, b) (* arity *)
    fun ^ (x, n) = List.tabulate (n, fn _ => x)
    infix 5 <> ->>
    infix 6 * ^
  in
    fun arity (THEN {bindings}) =
          [ [] * [] <> TAC
          , (EXP ^ bindings) * [] <> TAC
          ] ->> TAC
      | arity (THENF {bindings,...}) =
          [ [] * [] <> TAC
          , (EXP ^ bindings) * [] <> TAC
          ] ->> TAC
      | arity (THENL {length}) =
          ([] * [] <> TAC) ^ (length + 1)
            ->> TAC
      | arity (INTRO ({term,...}, _)) =
          (if term then [[] * [] <> EXP] else [])
            ->> TAC
      | arity (ELIM ({term,...}, _)) =
          (if term then [[] * [] <> EXP] else [])
            ->> TAC
      | arity (HYP _) =
          [] ->> TAC
  end

  fun support (ELIM ({target,...}, _)) = [(target, EXP)]
    | support (HYP ({target}, _)) = [(target, EXP)]
    | support _ = []

  structure Presheaf =
  struct
    type 'i t = 'i t
    fun map _ = raise Match
  end

  structure Eq =
  struct
    type 'i t = 'i t
    fun eq _ = raise Match
  end

  structure Show =
  struct
    type 'i t = 'i t
    fun toString _ = raise Match
  end
end
