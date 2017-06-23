signature REDPRL_ERROR =
sig
  datatype 'a frag =
     % of string
   | ! of 'a

  type term

  val error : term frag list -> exn
  val format : exn -> Fpp.doc

  val annotate : Pos.t option -> exn -> exn
  val annotation : exn -> Pos.t option
end
