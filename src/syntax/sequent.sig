signature SEQUENT =
sig
  type prop
  type expr
  type sort
  type var

  type metactx (* metavariable context *)
  type hypctx (* hypothesis contexts *)

  type context

  val emptyContext : context
  val getHyps : context -> hypctx
  val getMetas : context -> metactx

  val updateHyps : (hypctx -> hypctx) -> context -> context
  val updateMetas : (metactx -> metactx) -> context -> context

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort
    | EQ_MEM of expr * expr * prop
    | MEM of expr * prop
    | EQ_SYN of expr * expr
    | SYN of expr

  datatype judgment =
      >> of context * concl (* categorical sequent *)
    | |> of (var * sort) list * judgment (* generic sequent *)

  val toString : judgment -> string
end
