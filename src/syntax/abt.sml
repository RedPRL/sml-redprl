structure Metavariable = AbtSymbol ()

structure Symbol = AbtSymbol ()

(* it will come in handy for variables and symbols to be of the same type *)
structure Variable = Symbol

structure RedPRLSort =
  LcsSort
    (structure AtomicSort = RedPRLAtomicSort
     val opidSort = SOME SortData.OPID)

structure RedPRLOperator =
  LcsOperator
    (structure V = RedPRLV and K = RedPRLK and D = RedPRLD
     val opidSort = SOME SortData.OPID
     val input = RedPRLK.input)

structure RedPRLArity = RedPRLOperator.Ar
structure RedPRLValence = RedPRLArity.Vl

structure RedPRLAst =
  Ast
    (structure Operator = RedPRLOperator
     structure Metavar = Metavariable)


structure RedPRLAbt =
  Abt
    (structure O = RedPRLOperator
     structure Metavar = Metavariable
     structure Var = Variable
     structure Sym = Symbol)

structure RedPRLAstToAbt =
  AstToAbt
    (structure Ast = RedPRLAst
     structure Abt = RedPRLAbt)

structure ShowAbt = PlainShowAbt (RedPRLAbt)
structure DebugShowAbt = DebugShowAbt (RedPRLAbt)
