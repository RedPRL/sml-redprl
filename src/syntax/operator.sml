structure Operator : OPERATOR =
struct
  open OperatorData
  structure Arity = Arity

  type 'i t = 'i operator

  fun arity (S theta) =
    ScriptOperator.arity theta

  fun support (S theta) =
    ScriptOperator.support theta

  structure Presheaf =
  struct
    type 'i t = 'i t
    fun map f (S theta) =
      S (ScriptOperator.Presheaf.map f theta)
  end

  structure Eq =
  struct
    type 'i t = 'i t
    fun eq f (S theta1, S theta2) =
      ScriptOperator.Eq.eq f (theta1, theta2)
  end

  structure Show =
  struct
    type 'i t = 'i t
    fun toString f (S theta) =
      ScriptOperator.Show.toString f theta
  end

end
