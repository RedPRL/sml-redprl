structure RedPrlError :> REDPRL_ERROR =
struct
  open RedPrlErrorData

  exception Err of error
  exception Pos of Pos.t * exn

  val errorToExn = 
    fn (SOME pos, err) => Pos (pos, Err err)
     | (NONE, err) => Err err

  fun raiseError err = raise Err err
  fun raiseAnnotatedError (pos, err) = raise Pos (pos, Err err)
  val raiseAnnotatedError' =
    fn (SOME pos, err) => raiseAnnotatedError (pos, err)
     | (NONE, err) => raiseError err

  fun addPosition (pos, exn) = 
    case (pos, exn) of 
       (_, Pos _) => exn
     | (SOME pos, _) => Pos (pos, exn)
     | _ => exn

  val formatError =
    fn IMPOSSIBLE doc => Fpp.hvsep
        [Fpp.text "The impossible happened!", doc,
         Fpp.text "Please report this bug."]
     | INVALID_ATOMIC_JUDGMENT doc => Fpp.hvsep
        [Fpp.text "Not a valid atomic judgment:", Fpp.nest 2 doc]
     | INVALID_DIMENSION doc => Fpp.hsep
        [Fpp.text "Not a valid dimension:", Fpp.nest 2 doc]
     | INVALID_LEVEL doc => Fpp.hsep
        [Fpp.text "Not a valid universe level:", Fpp.nest 2 doc]
     | NOT_APPLICABLE (tool, obj) => Fpp.hsep
        [tool, Fpp.text "is not applicable to:", Fpp.nest 2 obj]
     | UNIMPLEMENTED doc => Fpp.hsep
        [Fpp.text "Not implemented:", Fpp.nest 2 doc]
     | INCORRECT_ARITY (ast, ar) =>
        Fpp.vsep
          [Fpp.hsep [Fpp.text "Incorrect arity in term:", Fpp.text (RedPrlAst.toString ast)],
           Fpp.hsep [Fpp.text "Expected: ", Fpp.text (RedPrlArity.toString ar)]]
     | GENERIC doc => Fpp.hsep doc

  val rec format =
    fn Err err => formatError err
     | Pos (_, exn) => format exn
     | RedPrlAbt.SortError {description,...} => Fpp.text description
     | RedPrlTacticMonad.Refine [] => Fpp.text "No solution found"
     | RedPrlTacticMonad.Refine exns => Fpp.vsep (List.map format exns)
     | exn => Fpp.text (exnMessage exn)

   val rec annotation =
     fn Pos (pos, exn) => 
        (case annotation exn of
            SOME pos' => SOME pos'
          | NONE => SOME pos)
      | RedPrlTacticMonad.Refine exns => annotationInExns exns
      | RedPrlAbt.SortError {annotation = ann,...} => ann
      | _ => NONE

  and annotationInExns = 
    fn [] => NONE
     | e::es => 
       (case annotation e of
           SOME p => SOME p
         | NONE => annotationInExns es)

  (* this is obsolete *)
  val error = Err o GENERIC
end
