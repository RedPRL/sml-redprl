structure AstSignatureDecl =
struct
  datatype 'd decl =
      DEF of 'd
    | SYM_DECL of RedPrlAtomicSort.t
end

(* All terms and expressions are treated as abstract syntax trees, and variables
 * and symbols have no identity other than their name. Identity and binding
 * structure will be imposed on variables and symbols in the next stage of
 * signature elaboration, [ABT_SIGNATURE]. *)
signature AST_SIGNATURE =
sig
  type term = RedPrlAst.ast
  type symbol = RedPrlAst.symbol
  type sort = RedPrlAtomicSort.t
  type metavariable = RedPrlAst.metavariable
  type valence = RedPrlAtomicValence.t

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  include SIGNATURE
    where type decl = def AstSignatureDecl.decl

  val def : def -> decl
  val symDecl : sort -> decl
end
