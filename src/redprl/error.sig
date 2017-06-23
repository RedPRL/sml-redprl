signature REDPRL_ERROR =
sig
  val error : Fpp.doc list -> exn
  val format : exn -> Fpp.doc

  val annotate : Pos.t option -> exn -> exn
  val annotation : exn -> Pos.t option
end
