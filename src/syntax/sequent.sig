signature SEQUENT =
sig
  type context
  type prop
  type sort
  type var

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort

  datatype sequent =
      >> of context * concl

  datatype generic =
      |> of (var * sort) list * sequent

  val toString : generic -> string
end
