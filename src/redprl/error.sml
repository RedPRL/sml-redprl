structure RedPrlError :> REDPRL_ERROR where type term = RedPrlAbt.abt =
struct
  datatype 'a err_frag =
     % of string
   | ! of 'a

  open RedPrlAbt
  structure ShowAbt = DebugShowAbt (RedPrlAbt)

  type term = abt

  exception E of term err_frag list
  val error = E

  val fragToString =
    fn % str => str
     | ! tm => "`" ^ ShowAbt.toString tm ^ "`"

  val format =
    fn E frags => ListSpine.pretty fragToString " " frags
     | exn => exnMessage exn
end
