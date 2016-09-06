signature REDPRL_ERROR =
sig
  datatype 'a err_frag =
     % of string
   | ! of 'a

  type term

  val error : term err_frag list -> exn
  val format : exn -> string
end
