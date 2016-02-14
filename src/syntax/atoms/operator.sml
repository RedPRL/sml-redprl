structure AtomsOperatorData =
struct
  datatype 'i atoms_operator =
      ATOM of Sort.t
    | TOKEN of 'i * Sort.t
end

structure AtomsOperator : OPERATOR =
struct
  open AtomsOperatorData SortData
  structure Arity = Arity
  type 'i t = 'i atoms_operator

  local
    fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
    fun op<> (a, b) = (a, b) (* valence *)
    fun op->> (a, b) = (a, b) (* arity *)
    fun op^ (x, n) = List.tabulate (n, fn _ => x)
    infix 5 <> ->>
    infix 6 * ^
  in
    val arity =
      fn ATOM tau =>
           [] ->> EXP
       | TOKEN (tau, u) =>
           [] ->> EXP
  end

  val support =
    fn ATOM tau => []
     | TOKEN (u,tau) => [(u,tau)]

  fun map f =
    fn ATOM tau => ATOM tau
     | TOKEN (u,tau) => TOKEN (f u, tau)

  fun eq f =
    fn (ATOM tau1, ATOM tau2) =>
          tau1 = tau2
     | (TOKEN (u, tau1), TOKEN (v, tau2)) =>
          tau1 = tau2 andalso f (u,v)
    | _ => false

  fun toString f =
    fn ATOM tau => "Atom{" ^ Sort.toString tau ^ "}"
     | TOKEN (u,tau) => "'" ^ f u ^ ":" ^ Sort.toString tau
end

