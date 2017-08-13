structure RedPrlError :> REDPRL_ERROR =
struct
  datatype Error
    = INVALID_DIMENSION of IntInf.int
    | INVALID_LEVEL of IntInf.int
    | UNIMPLEMENTED of Fpp.doc
    | GENERIC of Fpp.doc list

  exception Err of Error
  exception Pos of Pos.t * exn

  fun raiseError err = raise Err err
  fun raiseAnnotatedError (pos, err) = raise Pos (pos, Err err)
  val raiseAnnotatedError' =
    fn (SOME pos, err) => raiseAnnotatedError (pos, err)
     | (NONE, err) => raiseError err

  fun annotateException pos thunk = thunk () handle exn => raise Pos (pos, exn)
  fun annotateException' (SOME pos) thunk = annotateException pos thunk
    | annotateException' NONE thunk = thunk ()

  (* this function will be replaced by raiseGeneric *)
  val error = Err o GENERIC

  val prettyIntInf = Fpp.text o IntInf.toString
  val formatError =
    fn INVALID_DIMENSION i => Fpp.hsep
        [Fpp.text "Number", prettyIntInf i, Fpp.text "is not a valid dimension constant." ]
     | INVALID_LEVEL i => Fpp.hsep
        [Fpp.text "Number", prettyIntInf i, Fpp.text "is not a valid universe level constant." ]
     | UNIMPLEMENTED doc => Fpp.hsep
        [Fpp.text "The function", doc, Fpp.text "is not implemented yet."]
     | GENERIC doc => Fpp.hsep doc
  val rec format =
    fn Err err => formatError err
     | Pos (_, exn) => format exn
     | RedPrlAbt.BadSubstMetaenv {description,...} => Fpp.text description
     | exn => Fpp.text (exnMessage exn)

   val rec annotation =
     fn Pos (pos, exn) => 
        (case annotation exn of
            SOME pos' => SOME pos'
          | NONE => SOME pos)
      | _ => NONE
end
