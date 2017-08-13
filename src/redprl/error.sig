signature REDPRL_ERROR =
sig
  datatype Error
    = INVALID_DIMENSION of IntInf.int
    | INVALID_LEVEL of IntInf.int
    | GENERIC of Fpp.doc list

  val raiseError : Error -> 'a

  val raiseAnnotatedError : Pos.t * Error -> 'a
  val raiseAnnotatedError' : Pos.t option * Error -> 'a
  val annotateException : Pos.t -> (unit -> 'a) -> 'a
  val annotateException' : Pos.t option -> (unit -> 'a) -> 'a

  val format : exn -> Fpp.doc
  val annotation : exn -> Pos.t option

  (* this is obsolete *)
  val error : Fpp.doc list -> exn
end
