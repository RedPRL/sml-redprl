signature SEQUENT =
sig
  type context
  type prop
  type sort

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort

  datatype sequent =
      >> of context * concl
    | GENERAL of (Abt.variable * sort) list * sequent

  val toString : sequent -> string
end
