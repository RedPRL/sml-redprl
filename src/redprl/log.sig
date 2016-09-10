signature REDPRL_LOG =
sig
  datatype level =
     INFO
   | WARN
   | DUMP
   | FAIL

  val print : level -> Pos.t option * string -> unit
end
