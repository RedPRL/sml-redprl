signature NOMINAL_LCF_STRUCTURE = 
sig
  (* A model begins with a tactic metalanguage. *)
  structure Lcf : LCF_UTIL

  (* The nominal character of the semantics is dealt with using a Brouwerian
   * spread, a space whose points are free choice sequences. A free choice
   * sequence is a stream of constructible objects which are chosen not by a
   * computable function, but by interaction with a subject (i.e. a user). *)
  structure Spr : SPREAD
end

(* A model of Nominal LCF consists in a tactic metalanguage, a spread of
 * sequences of atoms, and an interpretation of the primitive rules of inference
 * into the metalanguage. *)
signature NOMINAL_LCF_MODEL =
sig
  include NOMINAL_LCF_STRUCTURE

  (* We will construct a model for a Nominal LCF theory [Syn]. *)
  structure Syn : NOMINAL_LCF_SYNTAX

  (* A "nominal" object is a functional which _continuously_ transforms a free
   * choice sequence into a result. *)
  type 'a nominal = Syn.atom Spr.point -> 'a

  type tactic = Lcf.jdg Lcf.tactic nominal
  type multitactic = Lcf.jdg Lcf.multitactic nominal

  (* An environment assigns a multitactic to each variable. *)
  type env = multitactic Syn.VarCtx.dict

  (* A model provides an interpretation of a refinement theory's primitive
   * rules of inference as nominal tactics, relative to a signature and
   * an environment.
   *
   * [Σ |=[ρ] rule ==> T] *)
  val rule : Syn.sign * env -> Syn.rule -> tactic

  val printHole : Syn.ann -> Lcf.jdg Lcf.state -> unit
end

