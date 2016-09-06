structure RedPrlError :> REDPRL_ERROR where type term = RedPrlAbt.abt =
struct
  datatype 'a err_frag =
     % of string
   | ! of 'a

  open RedPrlAbt
  structure ShowAbt = DebugShowAbt (RedPrlAbt)

  type term = abt

  exception E of term err_frag list
  exception Pos of Pos.t * exn

  val error = E

  val fragToString =
    fn % str => str
     | ! tm => "`" ^ ShowAbt.toString tm ^ "`"

  val rec format =
    fn E frags => ListSpine.pretty fragToString " " frags
     | Pos (_, exn) => format exn
     | exn => exnMessage exn

   fun annotate (SOME pos) exn = Pos (pos, exn)
     | annotate NONE exn = exn

   val annotation =
     fn Pos (pos, _) => SOME pos
      | _ => NONE
end
