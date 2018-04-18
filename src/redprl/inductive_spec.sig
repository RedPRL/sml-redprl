signature INDUCTIVE_SPEC =
sig
  type conid = string
  structure ConstrDict : DICT where type key = conid
  type decl
  type constr
  type constrs = (conid * constr) list

  type precomputed_valences
  val eqPrecomputedValences : precomputed_valences * precomputed_valences -> bool

  (* Given a data declaration, generate a list of sequents for type-checking. *)
  val checkDecl : decl -> Sequent.jdg list

  (* Valence collectors. *)
  val computeValences : RedPrlAst.ast -> precomputed_valences
  val getTypeValences : precomputed_valences -> RedPrlArity.valence list
  val getIntroValences : precomputed_valences -> conid -> RedPrlArity.valence list
  val getElimCasesValences : precomputed_valences -> RedPrlArity.valence list
  val computeAllSpecIntroValences : RedPrlAst.ast -> RedPrlArity.valence list ConstrDict.dict

  (* Used by the machine. *)
  val fillFamily : decl -> RedPrlAbt.abt list -> RedPrlAbt.abt list * constrs * RedPrlAbt.abt list
  val realizeIntroBoundaries : MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)
    -> constr -> RedPrlAbt.abt list -> RedPrlAbt.abt SyntaxView.boundary list
  val fillBranch : (RedPrlAbt.abt -> RedPrlAbt.abt)
    -> constr -> Sym.t list * RedPrlAbt.abt -> RedPrlAbt.abt list -> RedPrlAbt.abt
  val stepCoeIntro : RedPrlAbt.abt * RedPrlAbt.abt
    -> Sym.t * ((MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)) * conid * constr)
    -> RedPrlAbt.abt list -> RedPrlAbt.abt

  (* Used by the refiner. *)
  val EqType : Sequent.hyps -> decl -> RedPrlAbt.abt list * RedPrlAbt.abt list -> AtomicJudgment.View.as_level * RedPrlKind.t -> Sequent.jdg list
  val EqIntro : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * RedPrlAbt.abt RedPrlAbt.bview list
    -> decl -> conid -> (RedPrlAbt.abt list * RedPrlAbt.abt list) * RedPrlAbt.abt list -> Sequent.jdg list
  val Elim : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)
    -> Sym.t * RedPrlAbt.abt -> constrs -> Sequent.jdg list * Sym.t list list * (RedPrlAbt.abt list -> Sequent.jdg list)
  val EqElimBranches : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * (RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt list)
    -> Sym.t * RedPrlAbt.abt -> constrs -> RedPrlAbt.abt RedPrlAbt.bview list * RedPrlAbt.abt RedPrlAbt.bview list
    -> Sequent.jdg list
end
