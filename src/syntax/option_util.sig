signature OPTION_UTIL =
sig
  val traverseOpt : ('a -> 'b option) -> 'a list -> 'b list option
  val ** : 'a option * 'b option -> ('a * 'b) option
end
