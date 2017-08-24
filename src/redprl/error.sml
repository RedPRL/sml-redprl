structure RedPrlError :> REDPRL_ERROR =
struct
  open RedPrlErrorData

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

  val formatError =
    fn INVALID_CATEGORICAL_JUDGMENT doc => Fpp.hvsep
        [Fpp.text "Not a valid categorical judgment:", Fpp.align doc]
     | INVALID_DIMENSION doc => Fpp.hsep
        [Fpp.text "Not a valid dimension:", Fpp.align doc]
     | INVALID_LEVEL doc => Fpp.hsep
        [Fpp.text "Not a valid universe level:", Fpp.align doc]
     | UNIMPLEMENTED doc => Fpp.hsep
        [Fpp.text "Not implemented:", Fpp.align doc]
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

  fun syntaxError pos err = raise Match

  (* this is obsolete *)
  val error = Err o GENERIC
end
