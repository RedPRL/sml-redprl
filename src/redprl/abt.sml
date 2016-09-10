structure Metavar = AbtSymbol ()
structure Sym = AbtSymbol ()
structure Var = Sym

local
  structure AbtKit =
  struct
    structure Sym = Sym
    structure Var = Var
    structure Metavar = Metavar
    structure O = RedPrlOperator and Operator = RedPrlOperator
    type annotation = Pos.t
  end
in
  structure RedPrlAst = AstUtil (Ast (AbtKit))
  structure RedPrlAbt = Abt (AbtKit)
  structure AstToAbt = AstToAbt (structure Ast = RedPrlAst and Abt = RedPrlAbt)
  structure ShowAbt = DebugShowAbt (RedPrlAbt)
end
