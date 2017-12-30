structure RedPrlErrorData =
struct
  datatype error =
     IMPOSSIBLE of Fpp.doc
   | INVALID_ATOMIC_JUDGMENT of Fpp.doc
   | INVALID_DIMENSION of Fpp.doc
   | INVALID_LEVEL of Fpp.doc
   | NOT_APPLICABLE of Fpp.doc * Fpp.doc
   | UNIMPLEMENTED of Fpp.doc
   | GENERIC of Fpp.doc list
   | INCORRECT_ARITY of RedPrlAst.ast * RedPrlArity.t
end

signature REDPRL_ERROR =
sig
  datatype error = datatype RedPrlErrorData.error

  val addPosition : Pos.t option * exn -> exn
  
  val errorToExn : Pos.t option * error -> exn
  
  val raiseError : error -> 'a

  val raiseAnnotatedError : Pos.t * error -> 'a
  val raiseAnnotatedError' : Pos.t option * error -> 'a

  val format : exn -> Fpp.doc
  val annotation : exn -> Pos.t option

  (* this is obsolete *)
  val error : Fpp.doc list -> exn
end
