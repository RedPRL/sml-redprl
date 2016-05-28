structure Metavariable = AbtSymbol ()

structure Symbol = AbtSymbol ()

(* it will come in handy for variables and symbols to be of the same type *)
structure Variable = Symbol

structure Ast =
  Ast
    (structure Operator = Operator
     structure Metavariable = Metavariable)

structure Abt =
  Abt
    (structure Operator = Operator
     structure Metavariable = Metavariable
     structure Variable = Variable
     structure Symbol = Symbol)

structure AstToAbt = AstToAbt (structure Ast = Ast and Abt = Abt)

structure ShowAbt = PlainShowAbt (Abt)
structure DebugShowAbt = DebugShowAbt (Abt)
