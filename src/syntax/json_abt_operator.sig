signature JSON_ABT_OPERATOR =
sig
  include ABT_OPERATOR

  val encode : ('a -> Json.json_value) -> 'a t -> Json.json_value
  val decode : (Json.json_value -> 'a option) -> Json.json_value -> 'a t option
end
