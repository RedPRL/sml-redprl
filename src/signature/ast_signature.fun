functor AstSignature
  (structure Arity : ARITY
   structure Ast : AST
   sharing type Ast.spine = Arity.Valence.Spine.t)
  :> SIGNATURE
      where type term = Ast.ast
      where type symbol = Ast.symbol
      where type sort = Arity.Valence.sort
      where type metavariable = Ast.metavariable
      where type valence = Arity.Valence.t
      where type notation = unit
  =
struct
  type term = Ast.ast
  type symbol = Ast.symbol
  type sort = Arity.Valence.sort
  type metavariable = Ast.metavariable
  type valence = Arity.Valence.t

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list
  type notation = unit

  datatype def = DEF of symbols * arguments * sort * term
  datatype def_view = datatype def

  type decl =
    {def : def,
     notation : notation option}

  type sign = decl StringTelescope.telescope

  exception InvalidDef

  fun def d = d
  fun view d = d
end

structure AstSignature = AstSignature (structure Arity = Arity and Ast = Ast)
