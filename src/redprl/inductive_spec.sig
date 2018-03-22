signature INDUCTIVE_SPEC =
sig
  type conid = string
  structure ConstrDict : DICT where type key = conid
  type decl = RedPrlAbt.abt (* XXX *)
  type constr = RedPrlAbt.abt (* XXX *)
  type decl_args = RedPrlAbt.abt RedPrlAbt.bview list
  type args = RedPrlAbt.abt list
  type precomputedArity
  val eqPrecomputedArity : precomputedArity * precomputedArity -> bool

  (* Given a data declaration, generate a list of sequents for type-checking. *)
  val checkDecl : decl -> Sequent.jdg list

  (* Valence collectors. *)
  val computeValences : RedPrlAst.ast -> precomputedArity
  val getTypeValences : precomputedArity -> RedPrlArity.valence list
  val getIntroValences : precomputedArity -> conid -> RedPrlArity.valence list
  val getElimValences : precomputedArity -> RedPrlArity.valence list
  val computeAllSpecIntroValences : RedPrlAst.ast -> RedPrlArity.valence list ConstrDict.dict

  (* Used by the machine. *)
  val realizeIntroBoundaries : MlId.t * precomputedArity * conid ->
    decl_args -> decl -> args -> RedPrlAbt.abt SyntaxView.boundary list

  (* Used by the refiner. *)
  (* val EqArgsForType : decl -> args * args -> Sequent.jdg list *)
  (* val EqArgsForIntro : decl -> conid -> (args * args) * args -> Sequent.jdg list *)
end
