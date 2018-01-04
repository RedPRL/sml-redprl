signature ML_ID = 
sig
  eqtype t

  val eq : t * t -> bool
  val compare : t * t -> order

  val new : unit -> t
  val fresh : string -> t
  val const : string -> t
  val toString : t -> string
end
