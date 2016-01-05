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
    fun arity THEN =
          [ [] * [] <> TAC
          , [] * [] <> TAC
          ] ->> TAC
      | arity (THENF _) =
          [ [] * [] <> TAC
          , [] * [] <> TAC
          ] ->> TAC
      | arity (THENL {length}) =
          ([] * [] <> TAC) ^ (length + 1)
            ->> TAC
      | arity _ =
          raise Fail "tbi"
  end

  fun support _ = raise Match

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
