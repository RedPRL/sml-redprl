signature SEQUENT =
sig
  type context
  type prop
  type sort

  datatype sequent = >> of context * (prop * sort)

  val toString : sequent -> string
end
