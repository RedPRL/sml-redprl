structure RedPrlErrorData =
struct
  datatype Error
    = INVALID_CATEGORICAL_JUDGMENT of Fpp.doc
    | INVALID_DIMENSION of Fpp.doc
    | INVALID_LEVEL of Fpp.doc
    | UNIMPLEMENTED of Fpp.doc
    | GENERIC of Fpp.doc list
end

signature REDPRL_ERROR =
sig
  datatype Error = datatype RedPrlErrorData.Error
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
