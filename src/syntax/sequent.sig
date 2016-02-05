signature SEQUENT =
sig
  type context
  type prop

  datatype sequent = >> of context * prop

  val toString : sequent -> string
end
