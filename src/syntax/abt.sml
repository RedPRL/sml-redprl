structure Metavariable = Symbol ()

structure Symbol = Symbol ()

(* it will come in handy for variables and symbols to be of the same type *)
structure Variable = Symbol

structure Metacontext =
  Metacontext
    (structure Metavariable = Metavariable
     structure Valence = Valence.Eq)

structure Ast =
  Ast
    (structure Operator = Operator
     structure Metavariable = Metavariable)

structure Abt =
  Abt
    (structure Operator = Operator
     structure Metavariable = Metavariable
     structure Metacontext = Metacontext
     structure Variable = Variable
     structure Symbol = Symbol)

structure AstToAbt = AstToAbt (structure Ast = Ast and Abt = Abt)
