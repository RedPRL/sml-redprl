signature INDUCTIVE_SPEC =
sig
  type conid = string
  structure ConstrDict : DICT where type key = conid
  type decl = RedPrlAbt.abt (* XXX *)
  type constr = RedPrlAbt.abt (* XXX *)
  type constrs = (conid * constr) list
  type decl_args = RedPrlAbt.abt RedPrlAbt.bview list
  type args = RedPrlAbt.abt list
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
  val fillFamily : decl -> args -> args * constrs * args
  val realizeIntroBoundaries : MlId.t * (RedPrlArity.valence list * precomputed_valences) * (decl_args * args)
    -> constr -> args -> RedPrlAbt.abt SyntaxView.boundary list
  val fillBranch : (RedPrlAbt.abt -> RedPrlAbt.abt)
    -> constr -> Sym.t list * RedPrlAbt.abt -> args -> RedPrlAbt.abt
  val stepCoeIntro : RedPrlAbt.abt * RedPrlAbt.abt
    -> Sym.t * ((MlId.t * (RedPrlArity.valence list * precomputed_valences) * (decl_args * args)) * conid * constr)
    -> args -> RedPrlAbt.abt

  (* Used by the refiner. *)
  val EqType : Sequent.hyps -> decl -> args * args -> AtomicJudgment.View.as_level * RedPrlKind.t -> Sequent.jdg list
  val EqIntro : Sequent.hyps -> MlId.t * (RedPrlArity.valence list * precomputed_valences) * decl_args
    -> decl -> conid -> (args * args) * args -> Sequent.jdg list
  (* val EqElim : *)
end
