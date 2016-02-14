structure AtomsOperatorData =
struct
  datatype 'i atoms_operator =
      ATOM of Sort.t
    | TOKEN of 'i * Sort.t
    | TEST of Sort.t * Sort.t
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
       | TEST (sigma, tau) =>
           [[] * [] <> EXP,
            [] * [] <> EXP,
            [] * [] <> tau,
            [] * [] <> tau]
             ->> tau
  end

  val support =
    fn ATOM tau => []
     | TOKEN (u,tau) => [(u,tau)]
     | TEST _ => []

  fun map f =
    fn ATOM tau => ATOM tau
     | TOKEN (u,tau) => TOKEN (f u, tau)
     | TEST (sigma, tau) => TEST (sigma, tau)

  fun eq f =
    fn (ATOM tau1, ATOM tau2) =>
          tau1 = tau2
     | (TOKEN (u, tau1), TOKEN (v, tau2)) =>
          tau1 = tau2 andalso f (u,v)
     | (TEST (sigma1, tau1), TEST (sigma2, tau2)) =>
          sigma1 = sigma2 andalso tau1 = tau2
     | _ => false

  fun toString f =
    fn ATOM tau => "Atom{" ^ Sort.toString tau ^ "}"
     | TOKEN (u, tau) => "'" ^ f u ^ ":" ^ Sort.toString tau
     | TEST (sigma, tau) => "ifeq{" ^ Sort.toString sigma ^ "," ^ Sort.toString tau ^ "}"
end

