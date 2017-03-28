structure RedPrlError :> REDPRL_ERROR where type term = RedPrlAbt.abt =
struct
  datatype 'a frag =
     % of string
   | ! of 'a

  open RedPrlAbt

  type term = abt

  exception E of term frag list
  exception Pos of Pos.t * exn

  val error = E

  val fragToString =
    fn % str => str
     | ! tm => "`" ^ TermPrinter.toString tm ^ "`"

  val rec format =
    fn E frags => ListSpine.pretty fragToString " " frags
     | Pos (_, exn) => format exn
     | BadSubstMetaenv {description,...} => description
     | exn => exnMessage exn

   fun annotate (SOME pos) exn = Pos (pos, exn)
     | annotate NONE exn = exn

   val annotation =
     fn Pos (pos, _) => SOME pos
      | _ => NONE
end
