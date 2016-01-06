structure Operator : OPERATOR =
struct
  open OperatorData
  structure Arity = Arity

  type 'i t = 'i operator

  local
    fun * (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun <> (a, b) = (a, b) (* valence *)
    fun ->> (a, b) = (a, b) (* arity *)
    fun ^ (x, n) = List.tabulate (n, fn _ => x)
    infix 5 <> ->>
    infix 6 * ^
  in
    fun arity theta =
      case theta of
           S theta =>
             ScriptOperator.arity theta
         | VEC_LIT (tau, len) =>
             ([] * [] <> tau) ^ len
               ->> SortData.VEC tau
  end

  fun support theta =
    case theta of
         S theta => ScriptOperator.support theta
       | VEC_LIT (tau, len) => []

  structure Presheaf =
  struct
    type 'i t = 'i t
    fun map f theta =
      case theta of
           S theta => S (ScriptOperator.Presheaf.map f theta)
         | VEC_LIT p => VEC_LIT p
  end

  structure Eq =
  struct
    type 'i t = 'i t
    fun eq f ops =
      case ops of
           (S theta1, S theta2) =>
             ScriptOperator.Eq.eq f (theta1, theta2)
         | (VEC_LIT p1, VEC_LIT p2) =>
             p1 = p2
         | _ =>
             false
  end

  structure Show =
  struct
    type 'i t = 'i t
    fun toString f theta =
      case theta of
           S theta =>
             ScriptOperator.Show.toString f theta
         | VEC_LIT (tau, m) =>
             "vec{" ^ Sort.Show.toString tau ^ "}"
  end

end
