structure ArityNotation =
struct
  fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
  fun op<> (a, b) = (a, b) (* valence *)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure RedPrlAtomicValence = AbtValence (structure S = RedPrlAtomicSort and Sp = ListSpine)
structure RedPrlAtomicArity = AbtArity (RedPrlAtomicValence)
