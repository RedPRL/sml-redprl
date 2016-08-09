(* cubical dimensions *)

signature OPERATOR_INDEX =
sig
  type 'i t

  val support : 'i t -> ('i * SortData.sort) list
  val eq : ('i * 'i -> bool) -> 'i t * 'i t -> bool
  val toString : ('i -> string) -> 'i t -> string
  val map : ('i -> 'j) -> 'i t -> 'j t

  val encode : ('i -> Json.json_value) -> 'i t -> Json.json_value
  val decode : (Json.json_value -> 'i option) -> Json.json_value -> 'i t option
end

signature DIM =
sig
  datatype 'i dim =
     NAME of 'i
   | DIM0
   | DIM1

  include OPERATOR_INDEX where type 'i t = 'i dim

  (* returns a (true, r') when the substitution affected the input *)
  val subst : ('i * 'i -> bool) -> 'i dim * 'i -> 'i dim -> bool * 'i dim
end

signature DIM_SPAN =
sig
  type 'i dim

  type 'i dim_span =
    {starting : 'i dim,
     ending : 'i dim}

  include OPERATOR_INDEX where type 'i t = 'i dim_span

  val new : 'i dim * 'i dim -> 'i dim_span

  (* returns a (true, r') when the substitution affected the input *)
  val subst : ('i * 'i -> bool) -> 'i dim * 'i -> 'i dim_span -> bool * 'i dim_span
end

signature DIM_VEC =
sig
  type 'i dim

  type 'i dim_vec = 'i dim list

  include OPERATOR_INDEX where type 'i t = 'i dim_vec

  (* returns a (true, r') when the substitution affected the input *)
  val subst : ('i * 'i -> bool) -> 'i dim * 'i -> 'i dim_vec -> bool * 'i dim_vec
end
