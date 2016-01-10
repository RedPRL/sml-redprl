structure AstSignature : AST_SIGNATURE =
struct
  type opid = string
  structure Telescope = StringTelescope

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

  type decl = def AstSignatureDecl.decl
  val def = AstSignatureDecl.DEF

  type sign = decl StringTelescope.telescope
end
