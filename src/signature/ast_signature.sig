structure AstSignatureDecl =
struct
  datatype 'd decl = DEF of 'd
end

signature AST_SIGNATURE =
sig
  type term = Ast.ast
  type symbol = Ast.symbol
  type sort = Arity.Valence.sort
  type metavariable = Ast.metavariable
  type valence = Arity.Valence.t

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
end
