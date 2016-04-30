signature SEQUENT =
sig
  type prop
  type expr
  type sort
  type var

  type metactx (* metavariable context *)
  type symctx (* symbolic parameter contexts *)
  type hypctx (* hypothesis contexts *)

  type context

  val emptyContext : context
  val getHyps : context -> hypctx
  val getSyms : context -> symctx
  val getMetas : context -> metactx

  val updateHyps : (hypctx -> hypctx) -> context -> context
  val updateSyms : (symctx -> symctx) -> context -> context
  val updateMetas : (metactx -> metactx) -> context -> context

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort
    | EQ_MEM of expr * expr * prop
    | EQ_NEU of expr * expr

  datatype sequent =
      >> of context * concl

  datatype generic =
      |> of (var * sort) list * sequent

  val toString : generic -> string
end
