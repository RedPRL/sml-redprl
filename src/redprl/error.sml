structure RedPrlError :> REDPRL_ERROR =
struct
  exception E of Fpp.doc
  exception Pos of Pos.t * exn

  val error = E o Fpp.hsep

  val rec format =
    fn E doc => doc
     | Pos (_, exn) => format exn
     | RedPrlAbt.BadSubstMetaenv {description,...} => Fpp.text description
     | exn => Fpp.text (exnMessage exn)

   fun annotate (SOME pos) exn = Pos (pos, exn)
     | annotate NONE exn = exn

   val annotation =
     fn Pos (pos, _) => SOME pos
      | _ => NONE
end
