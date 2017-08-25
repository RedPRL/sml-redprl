structure RedPrlErrorData =
struct
  datatype error =
     INVALID_CATEGORICAL_JUDGMENT of Fpp.doc
   | INVALID_DIMENSION of Fpp.doc
   | INVALID_LEVEL of Fpp.doc
   | UNIMPLEMENTED of Fpp.doc
   | GENERIC of Fpp.doc list
end

signature REDPRL_ERROR =
sig
  datatype error = datatype RedPrlErrorData.error

  val errorToExn : Pos.t option * error -> exn
  
  val raiseError : error -> 'a

  val raiseAnnotatedError : Pos.t * error -> 'a
  val raiseAnnotatedError' : Pos.t option * error -> 'a
  val annotateException : Pos.t -> (unit -> 'a) -> 'a
  val annotateException' : Pos.t option -> (unit -> 'a) -> 'a

  val format : exn -> Fpp.doc
  val annotation : exn -> Pos.t option

  (* this is obsolete *)
  val error : Fpp.doc list -> exn
end
