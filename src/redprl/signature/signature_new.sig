signature SIGNATURE_SYN = 
sig
  type 'a m

  type env
  type src
  type t

  val resolve : env -> src -> t m
end

signature SIGNATURE_NEW = 
sig
  type 'a m

(*
  type value
  type src_cmd
  type elab_cmd

  val resolveCmd : env -> src_cmd -> elab_cmd m

  val eval : env -> elab_cmd -> value m
  *)
end
