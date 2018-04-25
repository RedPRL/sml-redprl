(* This isolates the parsing and checking of the inductive types
 * as much as possible from the rest of RedPRL. *)
signature INDUCTIVE_SPEC =
sig
  type conid = string
  structure ConstrDict : DICT where type key = conid
  type decl
  type constr
  type constrs = (conid * constr) list (* TODO make constrs abstract *)

  type precomputed_valences
  val eqPrecomputedValences : precomputed_valences * precomputed_valences -> bool

  (* Given a data declaration, generate a list of sequents for type-checking. *)
  val checkDecl : decl -> Sequent.jdg list

  (* The following functions extract the valences before the elaboration
   * so that sort-checking can be easily done. Note that this does not
   * handle meta-variables, which are taken care of by the meta language. *)
  (* Precompute the valences and keep them into an abstract data structure. *)
  val computeValences : RedPrlAst.ast -> precomputed_valences
  (* Get the valences of the type. *)
  val getTypeValences : precomputed_valences -> RedPrlArity.valence list
  (* Get the valences of the constructor. This includes the part associated with the type. *)
  val getIntroValences : precomputed_valences -> conid -> RedPrlArity.valence list
  (* Get the valences of the eliminator *after* the eliminated term. *)
  val getElimCasesValences : precomputed_valences -> RedPrlArity.valence list
  (* Get the valences of the constructors in the specification language. *)
  val computeAllSpecIntroValences : RedPrlAst.ast -> RedPrlArity.valence list ConstrDict.dict

  (* The following functions are helper functions to extract or manipulate the declaration
   * of the inductive types. *)

  (* Get the instance of the inductive type, given a list of arguments. The unused arguments are
   * returned as well, which might be useful for handling `elim` and `intro`. *)
  val fillFamily : decl -> RedPrlAbt.abt list -> RedPrlAbt.abt list * constrs * RedPrlAbt.abt list
  (* Get the boundaries of a particular constructor given the full list of arguments. *)
  val realizeIntroBoundaries : MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)
    -> constr -> RedPrlAbt.abt list -> RedPrlAbt.abt SyntaxView.boundary list
  (* Get the result of a case analysis, given the arguments from the pattern matching.
   * The first argument is the function applied to recursive arguments. *)
  val fillBranch : (RedPrlAbt.abt -> RedPrlAbt.abt)
    -> constr -> Sym.t list * RedPrlAbt.abt -> RedPrlAbt.abt list -> RedPrlAbt.abt
  (* The result of the coercion of a constructor. *)
  val stepCoeIntro : RedPrlAbt.abt * RedPrlAbt.abt
    -> Sym.t * ((MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)) * conid * constr)
    -> RedPrlAbt.abt list -> RedPrlAbt.abt

  (* The following functions are the type-checking code isolated from the refiner.
   * The principle is that the refiner should not know how exactly an inductive type
   * is defined.
   *
   * They are all generating sequents, not goals! It is the refiner which calls
   * these functions and turns sequents into subgoals. *)

  (* This is to compare two lists of arguments to some inductive types (not including meta variables). *)
  val EqType : Sequent.hyps -> decl -> RedPrlAbt.abt list * RedPrlAbt.abt list -> AtomicJudgment.View.as_level * RedPrlKind.t -> Sequent.jdg list
  (* This is to compare two lists of arguments to some constructor and a list of arguments to the type. *)
  val EqIntro : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * RedPrlAbt.abt RedPrlAbt.bview list
    -> decl -> conid -> (RedPrlAbt.abt list * RedPrlAbt.abt list) * RedPrlAbt.abt list -> Sequent.jdg list
  (* Given the motive and the term to be eliminated, return a list of sequents for type checking,
   * a list of lists of variables used in each branch, and a function to generate the coherence conditions. *)
  val Elim : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)
    -> Sym.t * RedPrlAbt.abt -> constrs -> Sequent.jdg list * Sym.t list list * (RedPrlAbt.abt list -> Sequent.jdg list)
  (* Given two elims, generate the sequents checking whether the branches are the same and they themselves are coherent.
   * Note that this does not type-check the motive(s). It is refiner's job to check the motive itself. *)
  val EqElimBranches : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)
    -> Sym.t * RedPrlAbt.abt -> constrs -> RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt RedPrlAbt.bview list
    -> Sequent.jdg list
end
