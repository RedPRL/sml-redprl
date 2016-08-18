structure AstSignature : AST_SIGNATURE =
struct
  structure Ast = RedPrlAst and Arity = RedPrlAtomicArity

  type opid = string
  structure Telescope = StringTelescope

  type term = Ast.ast
  type symbol = Ast.symbol
  type sort = Arity.Vl.sort
  type metavariable = Ast.metavariable
  type valence = Arity.Vl.t

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  type decl = def AstSignatureDecl.decl
  val def = AstSignatureDecl.DEF
  val symDecl = AstSignatureDecl.SYM_DECL

  type sign = (decl * Pos.t option) StringTelescope.telescope
end
