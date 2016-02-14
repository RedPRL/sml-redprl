structure AstSignatureDecl =
struct
  datatype 'd decl =
      DEF of 'd
    | SYMDCL of Sort.t
end

(* At this stage, a signature has only one form of declaration, definitions.
 * All terms and expressions are treated as abstract syntax trees, and variables
 * and symbols have no identity other than their name. Identity and binding
 * structure will be imposed on variables and symbols in the next stage of
 * signature elaboration, [ABT_SIGNATURE]. *)
signature AST_SIGNATURE =
sig
  type term = Ast.ast
  type symbol = Ast.symbol
  type sort = Sort.t
  type metavariable = Ast.metavariable
  type valence = Valence.t

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
  val symdcl : sort -> decl
end
