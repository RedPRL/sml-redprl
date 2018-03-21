structure Tm = RedPrlAbt

(* This is the core of name resolution for the metalanguage and the object language. *)
signature RESOLVER = 
sig
  type env
  type spec_env
  type mltype

  type id
  
  val init : env
  val spec_init : spec_env

  val lookupId : env -> Pos.t option -> id -> mltype
  val extendId : env -> id -> mltype -> env

  val lookupVar : env -> Pos.t option -> string -> Tm.variable * Tm.sort
  val lookupMeta : env -> Pos.t option -> string -> Tm.metavariable * Tm.valence

  val extendVars : env -> string list * Tm.sort list -> (Tm.variable * Tm.sort) list * env
  val extendMetas : env -> string list * Tm.valence list -> (Tm.metavariable * Tm.valence) list * env

  val lookupSpecIntro : spec_env -> Pos.t option -> InductiveSpec.conid -> Tm.valence list
  val makeSpecEnv : Tm.valence list InductiveSpec.ConstrDict.dict -> spec_env
end
